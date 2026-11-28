import OMAReductions.R_Erdos128_erdos_128_R2

/-!
# Theorem I1: Elementary All-Finite-n 3-Colorability for 14 * δ(G) >= 5 * n

Proves `colorable_three_of_fourteen_fifths`: every triangle-free graph `G` on `n` vertices
with `14 * δ(G) >= 5 * n` is 3-colorable (`G.Colorable 3`).
Closes 100% of `Erdos128.erdos_128.R2.H1` (Norin-Yepremyan 2015 threshold `5n/14`).
-/

-- Step Erdos128.erdos_128.R2.H1: hypothesis H1 of reduction Erdos128.erdos_128.R2
-- Credit: @iskamag

namespace Erdos128R2H1

open Finset SimpleGraph

/-- Indicator bound: `(if p then 1 else 0) <= 1`. -/
lemma ite_one_le (p : Prop) [Decidable p] : (if p then 1 else 0) ≤ 1 := by split_ifs <;> omega

lemma fin5_shift_1 (i r : Fin 5) : i + 1 + r = i + r + 1 := by fin_cases i <;> fin_cases r <;> decide
lemma fin5_shift_4 (i r : Fin 5) : i + r + 4 = i + 4 + r := by fin_cases i <;> fin_cases r <;> decide

/-- The 11 independent-set indicator vectors of C_5. -/
lemma c5_indep_cases {b0 b1 b2 b3 b4 : ℕ}
    (h0 : b0 ≤ 1) (h1 : b1 ≤ 1) (h2 : b2 ≤ 1) (h3 : b3 ≤ 1) (h4 : b4 ≤ 1)
    (e01 : b0 + b1 ≤ 1) (e12 : b1 + b2 ≤ 1) (e23 : b2 + b3 ≤ 1)
    (e34 : b3 + b4 ≤ 1) (e40 : b4 + b0 ≤ 1) :
    (b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0) ∨
    (b0 = 1 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0) ∨
    (b0 = 0 ∧ b1 = 1 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 0) ∨
    (b0 = 0 ∧ b1 = 0 ∧ b2 = 1 ∧ b3 = 0 ∧ b4 = 0) ∨
    (b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 1 ∧ b4 = 0) ∨
    (b0 = 0 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 1) ∨
    (b0 = 0 ∧ b1 = 1 ∧ b2 = 0 ∧ b3 = 0 ∧ b4 = 1) ∨
    (b0 = 1 ∧ b1 = 0 ∧ b2 = 1 ∧ b3 = 0 ∧ b4 = 0) ∨
    (b0 = 0 ∧ b1 = 1 ∧ b2 = 0 ∧ b3 = 1 ∧ b4 = 0) ∨
    (b0 = 0 ∧ b1 = 0 ∧ b2 = 1 ∧ b3 = 0 ∧ b4 = 1) ∨
    (b0 = 1 ∧ b1 = 0 ∧ b2 = 0 ∧ b3 = 1 ∧ b4 = 0) := by
  have hb0 : b0 = 0 ∨ b0 = 1 := by omega
  have hb1 : b1 = 0 ∨ b1 = 1 := by omega
  have hb2 : b2 = 0 ∨ b2 = 1 := by omega
  have hb3 : b3 = 0 ∨ b3 = 1 := by omega
  have hb4 : b4 = 0 ∨ b4 = 1 := by omega
  rcases hb0 with rfl | rfl <;> rcases hb1 with rfl | rfl <;> rcases hb2 with rfl | rfl <;>
    rcases hb3 with rfl | rfl <;> rcases hb4 with rfl | rfl <;> omega

-- Top-level pure-ℕ local weight caps for the 8 canonical J-orbits
lemma cap_case0 {b0 b1 b2 b3 b4 bv : ℕ}
    (hb0 : b0 ≤ 1) (hb1 : b1 ≤ 1) (hb2 : b2 ≤ 1) (hb3 : b3 ≤ 1) (hb4 : b4 ≤ 1) (hbv : bv ≤ 1)
    (e01 : b0 + b1 ≤ 1) (e12 : b1 + b2 ≤ 1) (e23 : b2 + b3 ≤ 1) (e34 : b3 + b4 ≤ 1) (e40 : b4 + b0 ≤ 1)
    (n0 : bv + b4 + b1 ≤ 2) (n1 : bv + b0 + b2 ≤ 2) (n2 : bv + b1 + b3 ≤ 2)
    (n3 : bv + b2 + b4 ≤ 2) (n4 : bv + b3 + b0 ≤ 2) :
    b0 + (b1 + (b2 + (b3 + (b4 + bv)))) ≤ 2 := by
  rcases c5_indep_cases hb0 hb1 hb2 hb3 hb4 e01 e12 e23 e34 e40 with
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;> omega

lemma cap_case1 {b0 b1 b2 b3 b4 bv bw0 bz0 bz2 bz3 : ℕ}
    (hb0 : b0 ≤ 1) (hb1 : b1 ≤ 1) (hb2 : b2 ≤ 1) (hb3 : b3 ≤ 1) (hb4 : b4 ≤ 1) (hbv : bv ≤ 1)
    (e01 : b0 + b1 ≤ 1) (e12 : b1 + b2 ≤ 1) (e23 : b2 + b3 ≤ 1) (e34 : b3 + b4 ≤ 1) (e40 : b4 + b0 ≤ 1)
    (n1 : bv + b0 + b2 ≤ 2) (n2 : bv + b1 + b3 ≤ 2) (n3 : bv + b2 + b4 ≤ 2) (n4 : bv + b3 + b0 ≤ 2)
    (w0v : bv + bw0 ≤ 1) (w04 : b4 + bw0 ≤ 1) (w01 : b1 + bw0 ≤ 1)
    (z0v : bv + bz0 ≤ 1) (z00 : b0 + bz0 ≤ 1)
    (z2v : bv + bz2 ≤ 1) (z22 : b2 + bz2 ≤ 1)
    (z3v : bv + bz3 ≤ 1) (z33 : b3 + bz3 ≤ 1) :
    2 * b0 + (b1 + (2 * b2 + (2 * b3 + (b4 + (4 * bv + (bw0 + (2 * bz0 + (bz2 + bz3)))))))) ≤ 6 := by
  rcases c5_indep_cases hb0 hb1 hb2 hb3 hb4 e01 e12 e23 e34 e40 with
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;> omega

lemma cap_case2 {b0 b1 b2 b3 b4 bv bw0 bw1 bz3 : ℕ}
    (hb0 : b0 ≤ 1) (hb1 : b1 ≤ 1) (hb2 : b2 ≤ 1) (hb3 : b3 ≤ 1) (hb4 : b4 ≤ 1) (hbv : bv ≤ 1)
    (e01 : b0 + b1 ≤ 1) (e12 : b1 + b2 ≤ 1) (e23 : b2 + b3 ≤ 1) (e34 : b3 + b4 ≤ 1) (e40 : b4 + b0 ≤ 1)
    (n2 : bv + b1 + b3 ≤ 2) (n3 : bv + b2 + b4 ≤ 2) (n4 : bv + b3 + b0 ≤ 2)
    (w0v : bv + bw0 ≤ 1) (w04 : b4 + bw0 ≤ 1) (w01 : b1 + bw0 ≤ 1)
    (w1v : bv + bw1 ≤ 1) (w10 : b0 + bw1 ≤ 1) (w12 : b2 + bw1 ≤ 1)
    (z3v : bv + bz3 ≤ 1) (z33 : b3 + bz3 ≤ 1) :
    b0 + (b1 + (2 * b2 + (3 * b3 + (2 * b4 + (2 * bv + (bw0 + (bw1 + bz3))))))) ≤ 5 := by
  rcases c5_indep_cases hb0 hb1 hb2 hb3 hb4 e01 e12 e23 e34 e40 with
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;> omega

lemma cap_case3 {b0 b1 b2 b3 b4 bv bw0 bw2 bz0 bz2 : ℕ}
    (hb0 : b0 ≤ 1) (hb1 : b1 ≤ 1) (hb2 : b2 ≤ 1) (hb3 : b3 ≤ 1) (hb4 : b4 ≤ 1) (hbv : bv ≤ 1)
    (e01 : b0 + b1 ≤ 1) (e12 : b1 + b2 ≤ 1) (e23 : b2 + b3 ≤ 1) (e34 : b3 + b4 ≤ 1) (e40 : b4 + b0 ≤ 1)
    (n1 : bv + b0 + b2 ≤ 2) (n3 : bv + b2 + b4 ≤ 2) (n4 : bv + b3 + b0 ≤ 2)
    (w0v : bv + bw0 ≤ 1) (w04 : b4 + bw0 ≤ 1) (w01 : b1 + bw0 ≤ 1)
    (w2v : bv + bw2 ≤ 1) (w21 : b1 + bw2 ≤ 1) (w23 : b3 + bw2 ≤ 1)
    (z0v : bv + bz0 ≤ 1) (z00 : b0 + bz0 ≤ 1)
    (z2v : bv + bz2 ≤ 1) (z22 : b2 + bz2 ≤ 1) :
    2 * b0 + (b1 + (2 * b2 + (b3 + (b4 + (4 * bv + (bw0 + (bw2 + (2 * bz0 + 2 * bz2)))))))) ≤ 6 := by
  have hbv' : bv = 0 ∨ bv = 1 := by omega
  rcases hbv' with rfl | rfl
  · rcases c5_indep_cases hb0 hb1 hb2 hb3 hb4 e01 e12 e23 e34 e40 with
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;> linarith
  · omega

lemma cap_case4 {b0 b1 b2 b3 b4 bv bw0 bw1 bw2 : ℕ}
    (hb0 : b0 ≤ 1) (hb1 : b1 ≤ 1) (hb2 : b2 ≤ 1) (hb3 : b3 ≤ 1) (hb4 : b4 ≤ 1) (hbv : bv ≤ 1)
    (e01 : b0 + b1 ≤ 1) (e12 : b1 + b2 ≤ 1) (e23 : b2 + b3 ≤ 1) (e34 : b3 + b4 ≤ 1) (e40 : b4 + b0 ≤ 1)
    (n3 : bv + b2 + b4 ≤ 2) (n4 : bv + b3 + b0 ≤ 2)
    (w0v : bv + bw0 ≤ 1) (w04 : b4 + bw0 ≤ 1) (w01 : b1 + bw0 ≤ 1)
    (w1v : bv + bw1 ≤ 1) (w10 : b0 + bw1 ≤ 1) (w12 : b2 + bw1 ≤ 1)
    (w2v : bv + bw2 ≤ 1) (w21 : b1 + bw2 ≤ 1) (w23 : b3 + bw2 ≤ 1) :
    2 * b0 + (b1 + (2 * b2 + (3 * b3 + (3 * b4 + (2 * bv + (bw0 + (2 * bw1 + bw2))))))) ≤ 6 := by
  have hbv' : bv = 0 ∨ bv = 1 := by omega
  rcases hbv' with rfl | rfl
  · rcases c5_indep_cases hb0 hb1 hb2 hb3 hb4 e01 e12 e23 e34 e40 with
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;> linarith
  · omega

lemma cap_case5 {b0 b1 b2 b3 b4 bv bw0 bw1 bw3 bz3 : ℕ}
    (hb0 : b0 ≤ 1) (hb1 : b1 ≤ 1) (hb2 : b2 ≤ 1) (hb3 : b3 ≤ 1) (hb4 : b4 ≤ 1) (hbv : bv ≤ 1)
    (e01 : b0 + b1 ≤ 1) (e12 : b1 + b2 ≤ 1) (e23 : b2 + b3 ≤ 1) (e34 : b3 + b4 ≤ 1) (e40 : b4 + b0 ≤ 1)
    (n2 : bv + b1 + b3 ≤ 2) (n4 : bv + b3 + b0 ≤ 2)
    (w0v : bv + bw0 ≤ 1) (w04 : b4 + bw0 ≤ 1) (w01 : b1 + bw0 ≤ 1)
    (w1v : bv + bw1 ≤ 1) (w10 : b0 + bw1 ≤ 1) (w12 : b2 + bw1 ≤ 1)
    (w3v : bv + bw3 ≤ 1) (w32 : b2 + bw3 ≤ 1) (w34 : b4 + bw3 ≤ 1)
    (z3v : bv + bz3 ≤ 1) (z33 : b3 + bz3 ≤ 1) :
    b0 + (b1 + (b2 + (2 * b3 + (b4 + (3 * bv + (bw0 + (bw1 + (bw3 + 2 * bz3)))))))) ≤ 5 := by
  have hbv' : bv = 0 ∨ bv = 1 := by omega
  rcases hbv' with rfl | rfl
  · rcases c5_indep_cases hb0 hb1 hb2 hb3 hb4 e01 e12 e23 e34 e40 with
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;> linarith
  · omega

lemma cap_case6 {b0 b1 b2 b3 b4 bv bw0 bw1 bw2 bw3 : ℕ}
    (hb0 : b0 ≤ 1) (hb1 : b1 ≤ 1) (hb2 : b2 ≤ 1) (hb3 : b3 ≤ 1) (hb4 : b4 ≤ 1) (hbv : bv ≤ 1)
    (e01 : b0 + b1 ≤ 1) (e12 : b1 + b2 ≤ 1) (e23 : b2 + b3 ≤ 1) (e34 : b3 + b4 ≤ 1) (e40 : b4 + b0 ≤ 1)
    (n4 : bv + b3 + b0 ≤ 2)
    (w0v : bv + bw0 ≤ 1) (w04 : b4 + bw0 ≤ 1) (w01 : b1 + bw0 ≤ 1)
    (w1v : bv + bw1 ≤ 1) (w10 : b0 + bw1 ≤ 1) (w12 : b2 + bw1 ≤ 1)
    (w2v : bv + bw2 ≤ 1) (w21 : b1 + bw2 ≤ 1) (w23 : b3 + bw2 ≤ 1)
    (w3v : bv + bw3 ≤ 1) (w32 : b2 + bw3 ≤ 1) (w34 : b4 + bw3 ≤ 1) :
    2 * b0 + (b1 + (b2 + (2 * b3 + (2 * b4 + (3 * bv + (bw0 + (2 * bw1 + (2 * bw2 + bw3)))))))) ≤ 6 := by
  have hbv' : bv = 0 ∨ bv = 1 := by omega
  rcases hbv' with rfl | rfl
  · rcases c5_indep_cases hb0 hb1 hb2 hb3 hb4 e01 e12 e23 e34 e40 with
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;> linarith
  · omega

lemma cap_case7 {b0 b1 b2 b3 b4 bv bw0 bw1 bw2 bw3 bw4 : ℕ}
    (hb0 : b0 ≤ 1) (hb1 : b1 ≤ 1) (hb2 : b2 ≤ 1) (hb3 : b3 ≤ 1) (hb4 : b4 ≤ 1) (hbv : bv ≤ 1)
    (e01 : b0 + b1 ≤ 1) (e12 : b1 + b2 ≤ 1) (e23 : b2 + b3 ≤ 1) (e34 : b3 + b4 ≤ 1) (e40 : b4 + b0 ≤ 1)
    (w0v : bv + bw0 ≤ 1) (w04 : b4 + bw0 ≤ 1) (w01 : b1 + bw0 ≤ 1)
    (w1v : bv + bw1 ≤ 1) (w10 : b0 + bw1 ≤ 1) (w12 : b2 + bw1 ≤ 1)
    (w2v : bv + bw2 ≤ 1) (w21 : b1 + bw2 ≤ 1) (w23 : b3 + bw2 ≤ 1)
    (w3v : bv + bw3 ≤ 1) (w32 : b2 + bw3 ≤ 1) (w34 : b4 + bw3 ≤ 1)
    (w4v : bv + bw4 ≤ 1) (w43 : b3 + bw4 ≤ 1) (w40 : b0 + bw4 ≤ 1) :
    3 * b0 + (3 * b1 + (3 * b2 + (3 * b3 + (3 * b4 + (4 * bv +
      (2 * bw0 + (2 * bw1 + (2 * bw2 + (2 * bw3 + 2 * bw4))))))))) ≤ 10 := by
  have hbv' : bv = 0 ∨ bv = 1 := by omega
  rcases hbv' with rfl | rfl
  · rcases c5_indep_cases hb0 hb1 hb2 hb3 hb4 e01 e12 e23 e34 e40 with
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;> linarith
  · omega

/-- All 32 subsets of Z_5 are cyclic rotations of 8 canonical subsets (no reflection needed). -/
lemma bool5_orbit (p : Fin 5 → Bool) :
    ∃ r : Fin 5,
      (p (0 + r) = false ∧ p (1 + r) = false ∧ p (2 + r) = false ∧ p (3 + r) = false ∧ p (4 + r) = false) ∨
      (p (0 + r) = true  ∧ p (1 + r) = false ∧ p (2 + r) = false ∧ p (3 + r) = false ∧ p (4 + r) = false) ∨
      (p (0 + r) = true  ∧ p (1 + r) = true  ∧ p (2 + r) = false ∧ p (3 + r) = false ∧ p (4 + r) = false) ∨
      (p (0 + r) = true  ∧ p (1 + r) = false ∧ p (2 + r) = true  ∧ p (3 + r) = false ∧ p (4 + r) = false) ∨
      (p (0 + r) = true  ∧ p (1 + r) = true  ∧ p (2 + r) = true  ∧ p (3 + r) = false ∧ p (4 + r) = false) ∨
      (p (0 + r) = true  ∧ p (1 + r) = true  ∧ p (2 + r) = false ∧ p (3 + r) = true  ∧ p (4 + r) = false) ∨
      (p (0 + r) = true  ∧ p (1 + r) = true  ∧ p (2 + r) = true  ∧ p (3 + r) = true  ∧ p (4 + r) = false) ∨
      (p (0 + r) = true  ∧ p (1 + r) = true  ∧ p (2 + r) = true  ∧ p (3 + r) = true  ∧ p (4 + r) = true) := by
  have h : ∀ (b0 b1 b2 b3 b4 : Bool),
      let q : Fin 5 → Bool := fun i => match i.val with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3 | _ => b4
      ∃ r : Fin 5,
        (q (0 + r) = false ∧ q (1 + r) = false ∧ q (2 + r) = false ∧ q (3 + r) = false ∧ q (4 + r) = false) ∨
        (q (0 + r) = true  ∧ q (1 + r) = false ∧ q (2 + r) = false ∧ q (3 + r) = false ∧ q (4 + r) = false) ∨
        (q (0 + r) = true  ∧ q (1 + r) = true  ∧ q (2 + r) = false ∧ q (3 + r) = false ∧ q (4 + r) = false) ∨
        (q (0 + r) = true  ∧ q (1 + r) = false ∧ q (2 + r) = true  ∧ q (3 + r) = false ∧ q (4 + r) = false) ∨
        (q (0 + r) = true  ∧ q (1 + r) = true  ∧ q (2 + r) = true  ∧ q (3 + r) = false ∧ q (4 + r) = false) ∨
        (q (0 + r) = true  ∧ q (1 + r) = true  ∧ q (2 + r) = false ∧ q (3 + r) = true  ∧ q (4 + r) = false) ∨
        (q (0 + r) = true  ∧ q (1 + r) = true  ∧ q (2 + r) = true  ∧ q (3 + r) = true  ∧ q (4 + r) = false) ∨
        (q (0 + r) = true  ∧ q (1 + r) = true  ∧ q (2 + r) = true  ∧ q (3 + r) = true  ∧ q (4 + r) = true) := by
    decide
  have heq : (fun i : Fin 5 => match i.val with | 0 => p 0 | 1 => p 1 | 2 => p 2 | 3 => p 3 | _ => p 4) = p := by
    funext i; fin_cases i <;> rfl
  have hinst := h (p 0) (p 1) (p 2) (p 3) (p 4)
  rwa [heq] at hinst

/-- Pure double-counting contradiction for a weighted vertex list `L : List (V × ℕ)`. -/
lemma weighted_list_contra {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h14d : ∀ x : V, 5 * Fintype.card V ≤ 14 * #(Finset.univ.filter (G.Adj x)))
    (L : List (V × ℕ)) (S M : ℕ)
    (hS : (L.map Prod.snd).sum = S)
    (hpt : ∀ y : V, (L.map (fun p => p.2 * if G.Adj y p.1 then 1 else 0)).sum ≤ M)
    (hkill : (0 < Fintype.card V ∧ 14 * M < 5 * S) ∨
      (14 * M ≤ 5 * S ∧ ∃ y₀ : V, (L.map (fun p => p.2 * if G.Adj y₀ p.1 then 1 else 0)).sum < M)) :
    False := by
  set n := Fintype.card V
  have hswap : ∀ K : List (V × ℕ),
      ∑ y : V, (K.map (fun p => p.2 * if G.Adj y p.1 then 1 else 0)).sum =
      (K.map (fun p => p.2 * #(Finset.univ.filter (G.Adj p.1)))).sum := by
    intro K; induction K with
    | nil => simp
    | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
      congr 1
      rw [← Finset.mul_sum, ← Finset.card_filter]
      congr 2; ext y; simp [G.adj_comm]
  have hlo : ∀ K : List (V × ℕ),
      5 * n * (K.map Prod.snd).sum ≤ 14 * (K.map (fun p => p.2 * #(Finset.univ.filter (G.Adj p.1)))).sum := by
    intro K; induction K with
    | nil => simp
    | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have hp := Nat.mul_le_mul_left p.2 (h14d p.1)
      have h1 : 5 * n * p.2 ≤ 14 * (p.2 * #(Finset.univ.filter (G.Adj p.1))) := by linarith
      have h2 : 5 * n * (p.2 + (rest.map Prod.snd).sum) = 5 * n * p.2 + 5 * n * (rest.map Prod.snd).sum := by ring
      have h3 : 14 * (p.2 * #(Finset.univ.filter (G.Adj p.1)) +
          (rest.map (fun p => p.2 * #(Finset.univ.filter (G.Adj p.1)))).sum) =
          14 * (p.2 * #(Finset.univ.filter (G.Adj p.1))) +
          14 * (rest.map (fun p => p.2 * #(Finset.univ.filter (G.Adj p.1)))).sum := by ring
      omega
  have hloL : 5 * n * S ≤ 14 * (L.map (fun p => p.2 * #(Finset.univ.filter (G.Adj p.1)))).sum := by
    rw [← hS]; exact hlo L
  rcases hkill with ⟨hn_pos, hstrict⟩ | ⟨hle, y₀, hy₀⟩
  · have hup : ∑ y : V, (L.map (fun p => p.2 * if G.Adj y p.1 then 1 else 0)).sum ≤ M * n := by
      calc _ ≤ ∑ _y : V, M := Finset.sum_le_sum (fun y _ => hpt y)
        _ = M * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    rw [hswap L] at hup
    have h1 : 5 * n * S ≤ 14 * M * n := by nlinarith only [hloL, hup]
    nlinarith only [h1, hstrict, hn_pos]
  · have hup : ∑ y : V, (L.map (fun p => p.2 * if G.Adj y p.1 then 1 else 0)).sum < M * n := by
      have hlt : ∑ y : V, (L.map (fun p => p.2 * if G.Adj y p.1 then 1 else 0)).sum < ∑ _y : V, M :=
        Finset.sum_lt_sum (fun y _ => hpt y) ⟨y₀, Finset.mem_univ y₀, hy₀⟩
      rwa [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at hlt
    rw [hswap L] at hup
    nlinarith only [hloL, hup, hle]

/-- Theorem I1 (Elementary All-Finite-n 3-Colorability for 14δ >= 5n):
    Every triangle-free graph `G` with `5 * n <= 14 * d(v)` for all `v` is 3-colorable. -/
theorem colorable_three_of_fourteen_fifths {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (h14d : ∀ v : V, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard) :
    G.Colorable 3 := by
  classical
  set n := Fintype.card V
  by_cases hn0 : n = 0
  · have hE : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
    exact ⟨SimpleGraph.Coloring.mk (fun x => (hE.false x).elim) (fun {a _} _ => (hE.false a).elim)⟩
  have hn_pos : 0 < n := by omega
  obtain ⟨M, hGM, hMTF, hMmax⟩ := OMA.R_Erdos128_erdos_128_R2.exists_maximal_triangleFree G hTF
  suffices hM3 : M.Colorable 3 by
    obtain ⟨c⟩ := hM3
    exact ⟨SimpleGraph.Coloring.mk (fun x => c x) (fun h => c.valid (hGM h))⟩
  by_contra hnot3
  have hdeg : ∀ x : V, 5 * n ≤ 14 * #(Finset.univ.filter (M.Adj x)) := by
    intro x
    have h1 := h14d x
    rw [Set.ncard_eq_toFinset_card'] at h1
    have hsub : (G.neighborSet x).toFinset ⊆ Finset.univ.filter (M.Adj x) := fun y hy =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGM (Set.mem_toFinset.mp hy)⟩
    have hle := Finset.card_le_card hsub
    omega
  have huniv_ne : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn_pos)
  obtain ⟨v, _, hv_min⟩ := Finset.exists_min_image Finset.univ (fun x => #(Finset.univ.filter (M.Adj x))) huniv_ne
  let I : Finset V := Finset.univ.filter (M.Adj v)
  have hdv_le : ∀ x : V, #I ≤ #(Finset.univ.filter (M.Adj x)) := fun x => hv_min x (Finset.mem_univ x)
  have h3dv : n < 3 * #I := by have := hdeg v; change 5 * n ≤ 14 * #I at this; omega
  let S : Set V := {w : V | w ∉ I}
  let H : SimpleGraph S := M.induce S
  have hH_TF : H.CliqueFree 3 := by
    intro t ht
    apply hMTF (t.image Subtype.val)
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact ht.1 ha hb (fun hab => hxy (congrArg Subtype.val hab))
    · rw [Finset.card_image_of_injective _ Subtype.val_injective, ht.2]
  have hH_not2 : ¬ H.Colorable 2 := by
    rintro ⟨c2⟩
    apply hnot3
    refine ⟨SimpleGraph.Coloring.mk (fun w =>
      if hw : w ∈ I then (2 : Fin 3) else ⟨(c2 ⟨w, hw⟩).val, by have := (c2 ⟨w, hw⟩).isLt; omega⟩) ?_⟩
    intro a b hab
    by_cases ha : a ∈ I <;> by_cases hb : b ∈ I
    · exfalso; exact OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hMTF
        (Finset.mem_filter.mp ha).2 hab (Finset.mem_filter.mp hb).2
    · simp only [ha, hb, dite_true, dite_false]; intro heq
      have hval := congrArg Fin.val heq; have hlt := (c2 ⟨b, hb⟩).isLt; dsimp only at hval; omega
    · simp only [ha, hb, dite_true, dite_false]; intro heq
      have hval := congrArg Fin.val heq; have hlt := (c2 ⟨a, ha⟩).isLt; dsimp only at hval; omega
    · simp only [ha, hb, dite_false]; intro heq
      have hval := congrArg Fin.val heq; dsimp only at hval
      exact c2.valid (show H.Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab) (Fin.ext hval)
  obtain ⟨L, hL_odd, hL5, hL_min, fH, hfH_loop, hfH_adj, _, _⟩ :=
    OMA.R_Erdos128_erdos_128_R2.exists_shortest_odd_walk_of_nonbip H hH_TF hH_not2
  let f : ℕ → V := fun i => (fH i).val
  have hf_loop : f L = f 0 := congrArg Subtype.val hfH_loop
  have hf_adj : ∀ i < L, M.Adj (f i) (f (i + 1)) := fun i hi => hfH_adj i hi
  have hf_notI : ∀ i : ℕ, f i ∉ I := fun i => (fH i).property
  -- Eliminate all L >= 7 using min-degree v: (L + 5) * #I <= 4 * n => 3 * #I <= n
  have hL_eq5 : L = 5 := by
    have hdeg_out : ∀ w : V, w ∉ I → #((Finset.range L).filter (fun i => M.Adj w (f i))) ≤ 2 := fun w hw =>
      OMA.R_Erdos128_erdos_128_R2.shortest_odd_walk_deg_le_two H hH_TF hL_odd hL5 hL_min hfH_loop hfH_adj ⟨w, hw⟩
    have hdeg_in : ∀ w : V, 2 * #((Finset.range L).filter (fun i => M.Adj w (f i))) ≤ L - 1 := by
      intro w
      set T := (Finset.range L).filter (fun i => M.Adj w (f i))
      have hinj : Set.InjOn (fun i : ℕ => (i + 1) % L) (T : Set ℕ) := by
        intro a ha b hb heq; dsimp only at heq
        have haL := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have hbL := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        by_cases ha1 : a + 1 < L <;> by_cases hb1 : b + 1 < L
        · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at heq; omega
        · rw [Nat.mod_eq_of_lt ha1, show b + 1 = L by omega, Nat.mod_self] at heq; omega
        · rw [show a + 1 = L by omega, Nat.mod_self, Nat.mod_eq_of_lt hb1] at heq; omega
        · omega
      have hdisj : Disjoint T (T.image (fun i => (i + 1) % L)) := by
        rw [Finset.disjoint_left]; intro j hjT hjIm
        obtain ⟨i, hiT, rfl⟩ := Finset.mem_image.mp hjIm
        have hiL := Finset.mem_range.mp (Finset.mem_filter.mp hiT).1
        have hwi := (Finset.mem_filter.mp hiT).2; have hwj := (Finset.mem_filter.mp hjT).2
        by_cases hi1 : i + 1 < L
        · rw [Nat.mod_eq_of_lt hi1] at hwj
          exact OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hMTF hwi (hf_adj i hiL) hwj
        · rw [show i + 1 = L by omega, Nat.mod_self] at hwj
          have hadj := hf_adj i hiL; rw [show i + 1 = L by omega, hf_loop] at hadj
          exact OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hMTF hwi hadj hwj
      have hsub : T ∪ T.image (fun i => (i + 1) % L) ⊆ Finset.range L := by
        refine Finset.union_subset (Finset.filter_subset _ _) ?_
        intro j hj; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
      have h2T : 2 * #T ≤ L := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj, Finset.card_range] at h1; omega
      obtain ⟨m, hm⟩ := hL_odd; omega
    have hsum_swap : ∑ i ∈ Finset.range L, #(Finset.univ.filter (M.Adj (f i))) =
        ∑ w : V, #((Finset.range L).filter (fun i => M.Adj w (f i))) := by
      simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro w _; apply Finset.sum_congr rfl; intro i _; simp [M.adj_comm]
    have hsum_up : 2 * ∑ i ∈ Finset.range L, #(Finset.univ.filter (M.Adj (f i))) ≤ 4 * (n - #I) + (L - 1) * #I := by
      rw [hsum_swap]
      have hpart : ∑ w : V, #((Finset.range L).filter (fun i => M.Adj w (f i))) =
          ∑ w ∈ Finset.univ \ I, #((Finset.range L).filter (fun i => M.Adj w (f i))) +
          ∑ w ∈ I, #((Finset.range L).filter (fun i => M.Adj w (f i))) := by
        rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset (Finset.subset_univ I)]
      have h1 : ∑ w ∈ Finset.univ \ I, #((Finset.range L).filter (fun i => M.Adj w (f i))) ≤ 2 * (n - #I) := by
        calc _ ≤ ∑ _w ∈ Finset.univ \ I, 2 := Finset.sum_le_sum (fun w hw => hdeg_out w (Finset.mem_sdiff.mp hw).2)
          _ = #(Finset.univ \ I) * 2 := by rw [Finset.sum_const, smul_eq_mul]
          _ = 2 * (n - #I) := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, mul_comm]
      have h2 : 2 * ∑ w ∈ I, #((Finset.range L).filter (fun i => M.Adj w (f i))) ≤ (L - 1) * #I := by
        rw [Finset.mul_sum]
        calc _ ≤ ∑ _w ∈ I, (L - 1) := Finset.sum_le_sum (fun w _ => hdeg_in w)
          _ = (L - 1) * #I := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      omega
    have hsum_lo : L * #I ≤ ∑ i ∈ Finset.range L, #(Finset.univ.filter (M.Adj (f i))) := by
      calc L * #I = ∑ _i ∈ Finset.range L, #I := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        _ ≤ ∑ i ∈ Finset.range L, #(Finset.univ.filter (M.Adj (f i))) := Finset.sum_le_sum (fun i _ => hdv_le (f i))
    have hI_le : #I ≤ n := (Finset.card_le_card (Finset.subset_univ I)).trans (by simp [n])
    have hlin : (L + 5) * #I ≤ 4 * n := by
      have h4n : 4 * (n - #I) + (L - 1) * #I = 4 * n + (L - 5) * #I := by
        zify [hI_le, hL5, show 1 ≤ L by omega]; ring
      rw [h4n] at hsum_up
      zify [hL5] at hsum_lo hsum_up ⊢; nlinarith only [hsum_lo, hsum_up]
    by_contra hne5
    obtain ⟨m, hm⟩ := hL_odd
    have hL7 : 7 ≤ L := by omega
    have h12 : 12 * #I ≤ (L + 5) * #I := Nat.mul_le_mul_right #I (by omega)
    omega
  -- Now L = 5: extract C_5 and rotate cyclically so J is canonical
  let a₀ : Fin 5 → V := fun i => f i.val
  have ha0_adj : ∀ i : Fin 5, M.Adj (a₀ i) (a₀ (i + 1)) := by
    intro i; fin_cases i
    · exact hf_adj 0 (by omega)
    · exact hf_adj 1 (by omega)
    · exact hf_adj 2 (by omega)
    · exact hf_adj 3 (by omega)
    · have h4 := hf_adj 4 (by omega); rw [show 4 + 1 = L by omega, hf_loop] at h4; exact h4
  have hv_a0 : ∀ i : Fin 5, ¬ M.Adj v (a₀ i) := fun i h =>
    hf_notI i.val (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  let P₀ : Fin 5 → Prop := fun i => ∃ w : V, M.Adj v w ∧ M.Adj w (a₀ (i + 4)) ∧ M.Adj w (a₀ (i + 1))
  obtain ⟨rot, horbit⟩ := bool5_orbit (fun i => decide (P₀ i))
  let a : Fin 5 → V := fun i => a₀ (i + rot)
  have ha_adj : ∀ i : Fin 5, M.Adj (a i) (a (i + 1)) := fun i => by
    dsimp only [a]; rw [fin5_shift_1]; exact ha0_adj (i + rot)
  have hv_a : ∀ i : Fin 5, ¬ M.Adj v (a i) := fun i => hv_a0 (i + rot)
  let J : Fin 5 → Prop := fun i => ∃ w : V, M.Adj v w ∧ M.Adj w (a (i + 4)) ∧ M.Adj w (a (i + 1))
  have hJ_iff : ∀ i : Fin 5, P₀ (i + rot) ↔ J i := fun i => by
    dsimp only [P₀, J, a]; rw [fin5_shift_4, ← fin5_shift_1]
  have hz_ex : ∀ k : Fin 5, ∃ z : V, M.Adj v z ∧ M.Adj z (a k) := fun k => by
    have hne : v ≠ a k := fun heq => hv_a (k + 1) (heq ▸ ha_adj k)
    obtain ⟨z, hvz, haz⟩ := hMmax v (a k) hne (hv_a k)
    exact ⟨z, hvz, haz.symm⟩
  have h_edge_le : ∀ (y x1 x2 : V), M.Adj x1 x2 →
      (if M.Adj y x1 then 1 else 0) + (if M.Adj y x2 then 1 else 0) ≤ 1 := fun y x1 x2 h12 => by
    by_cases h1 : M.Adj y x1 <;> by_cases h2 : M.Adj y x2
    · exact (OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hMTF h1 h12 h2).elim
    all_goals simp [h1, h2]
  have h_notJ_le : ∀ (i : Fin 5), ¬ J i → ∀ y : V,
      (if M.Adj y v then 1 else 0) + (if M.Adj y (a (i + 4)) then 1 else 0) +
      (if M.Adj y (a (i + 1)) then 1 else 0) ≤ 2 := fun i hni y => by
    by_cases hv' : M.Adj y v <;> by_cases h4 : M.Adj y (a (i + 4)) <;> by_cases h1 : M.Adj y (a (i + 1))
    · exact (hni ⟨y, hv'.symm, h4, h1⟩).elim
    all_goals simp [hv', h4, h1]
  have hJ_true : ∀ {i : Fin 5}, decide (P₀ (i + rot)) = true → J i := fun h => (hJ_iff _).mp (of_decide_eq_true h)
  have hJ_false : ∀ {i : Fin 5}, decide (P₀ (i + rot)) = false → ¬ J i := fun h hji =>
    of_decide_eq_false h ((hJ_iff _).mpr hji)
  have ha01 : M.Adj (a 0) (a 1) := ha_adj 0
  have ha12 : M.Adj (a 1) (a 2) := ha_adj 1
  have ha23 : M.Adj (a 2) (a 3) := ha_adj 2
  have ha34 : M.Adj (a 3) (a 4) := ha_adj 3
  have ha40 : M.Adj (a 4) (a 0) := ha_adj 4
  -- Dispatch the 8 canonical cyclic orbits of J via top-level cap lemmas
  rcases horbit with ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ |
    ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩ |
    ⟨h0, h1, h2, h3, h4⟩ | ⟨h0, h1, h2, h3, h4⟩
  · -- Case 1: J = ∅; S = 6, M = 2
    refine weighted_list_contra M hdeg [(a 0, 1), (a 1, 1), (a 2, 1), (a 3, 1), (a 4, 1), (v, 1)] 6 2
      rfl (fun y => ?_) (Or.inl ⟨hn_pos, by decide⟩)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    exact cap_case0 (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _)
      (h_edge_le y _ _ ha01) (h_edge_le y _ _ ha12) (h_edge_le y _ _ ha23) (h_edge_le y _ _ ha34) (h_edge_le y _ _ ha40)
      (h_notJ_le 0 (hJ_false h0) y) (h_notJ_le 1 (hJ_false h1) y) (h_notJ_le 2 (hJ_false h2) y)
      (h_notJ_le 3 (hJ_false h3) y) (h_notJ_le 4 (hJ_false h4) y)
  · -- Case 2: J = {0}, K = {0, 2, 3}; S = 17, M = 6
    obtain ⟨w0, hw0v, hw04, hw01⟩ := hJ_true h0
    obtain ⟨z0, hz0v, hz0a⟩ := hz_ex 0
    obtain ⟨z2, hz2v, hz2a⟩ := hz_ex 2
    obtain ⟨z3, hz3v, hz3a⟩ := hz_ex 3
    refine weighted_list_contra M hdeg
      [(a 0, 2), (a 1, 1), (a 2, 2), (a 3, 2), (a 4, 1), (v, 4), (w0, 1), (z0, 2), (z2, 1), (z3, 1)] 17 6
      rfl (fun y => ?_) (Or.inl ⟨hn_pos, by decide⟩)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    exact cap_case1 (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _)
      (h_edge_le y _ _ ha01) (h_edge_le y _ _ ha12) (h_edge_le y _ _ ha23) (h_edge_le y _ _ ha34) (h_edge_le y _ _ ha40)
      (h_notJ_le 1 (hJ_false h1) y) (h_notJ_le 2 (hJ_false h2) y) (h_notJ_le 3 (hJ_false h3) y) (h_notJ_le 4 (hJ_false h4) y)
      (h_edge_le y _ _ hw0v) (h_edge_le y _ _ hw04.symm) (h_edge_le y _ _ hw01.symm)
      (h_edge_le y _ _ hz0v) (h_edge_le y _ _ hz0a.symm)
      (h_edge_le y _ _ hz2v) (h_edge_le y _ _ hz2a.symm)
      (h_edge_le y _ _ hz3v) (h_edge_le y _ _ hz3a.symm)
  · -- Case 3: J = {0, 1}, K = {3}; S = 14, M = 5, SLACK at y = v
    obtain ⟨w0, hw0v, hw04, hw01⟩ := hJ_true h0
    obtain ⟨w1, hw1v, hw10, hw12⟩ := hJ_true h1
    obtain ⟨z3, hz3v, hz3a⟩ := hz_ex 3
    refine weighted_list_contra M hdeg
      [(a 0, 1), (a 1, 1), (a 2, 2), (a 3, 3), (a 4, 2), (v, 2), (w0, 1), (w1, 1), (z3, 1)] 14 5
      rfl (fun y => ?_) (Or.inr ⟨by decide, v, ?_⟩)
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
      exact cap_case2 (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _)
        (h_edge_le y _ _ ha01) (h_edge_le y _ _ ha12) (h_edge_le y _ _ ha23) (h_edge_le y _ _ ha34) (h_edge_le y _ _ ha40)
        (h_notJ_le 2 (hJ_false h2) y) (h_notJ_le 3 (hJ_false h3) y) (h_notJ_le 4 (hJ_false h4) y)
        (h_edge_le y _ _ hw0v) (h_edge_le y _ _ hw04.symm) (h_edge_le y _ _ hw01.symm)
        (h_edge_le y _ _ hw1v) (h_edge_le y _ _ hw10.symm) (h_edge_le y _ _ hw12.symm)
        (h_edge_le y _ _ hz3v) (h_edge_le y _ _ hz3a.symm)
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul,
        hv_a 0, hv_a 1, hv_a 2, hv_a 3, hv_a 4, M.loopless.irrefl v, hw0v, hw1v, hz3v, ite_false, ite_true]
      decide
  · -- Case 4: J = {0, 2}, K = {0, 2}; S = 17, M = 6
    obtain ⟨w0, hw0v, hw04, hw01⟩ := hJ_true h0
    obtain ⟨w2, hw2v, hw21, hw23⟩ := hJ_true h2
    obtain ⟨z0, hz0v, hz0a⟩ := hz_ex 0
    obtain ⟨z2, hz2v, hz2a⟩ := hz_ex 2
    refine weighted_list_contra M hdeg
      [(a 0, 2), (a 1, 1), (a 2, 2), (a 3, 1), (a 4, 1), (v, 4), (w0, 1), (w2, 1), (z0, 2), (z2, 2)] 17 6
      rfl (fun y => ?_) (Or.inl ⟨hn_pos, by decide⟩)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    exact cap_case3 (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _)
      (h_edge_le y _ _ ha01) (h_edge_le y _ _ ha12) (h_edge_le y _ _ ha23) (h_edge_le y _ _ ha34) (h_edge_le y _ _ ha40)
      (h_notJ_le 1 (hJ_false h1) y) (h_notJ_le 3 (hJ_false h3) y) (h_notJ_le 4 (hJ_false h4) y)
      (h_edge_le y _ _ hw0v) (h_edge_le y _ _ hw04.symm) (h_edge_le y _ _ hw01.symm)
      (h_edge_le y _ _ hw2v) (h_edge_le y _ _ hw21.symm) (h_edge_le y _ _ hw23.symm)
      (h_edge_le y _ _ hz0v) (h_edge_le y _ _ hz0a.symm)
      (h_edge_le y _ _ hz2v) (h_edge_le y _ _ hz2a.symm)
  · -- Case 5: J = {0, 1, 2}, K = ∅; S = 17, M = 6
    obtain ⟨w0, hw0v, hw04, hw01⟩ := hJ_true h0
    obtain ⟨w1, hw1v, hw10, hw12⟩ := hJ_true h1
    obtain ⟨w2, hw2v, hw21, hw23⟩ := hJ_true h2
    refine weighted_list_contra M hdeg
      [(a 0, 2), (a 1, 1), (a 2, 2), (a 3, 3), (a 4, 3), (v, 2), (w0, 1), (w1, 2), (w2, 1)] 17 6
      rfl (fun y => ?_) (Or.inl ⟨hn_pos, by decide⟩)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    exact cap_case4 (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _)
      (h_edge_le y _ _ ha01) (h_edge_le y _ _ ha12) (h_edge_le y _ _ ha23) (h_edge_le y _ _ ha34) (h_edge_le y _ _ ha40)
      (h_notJ_le 3 (hJ_false h3) y) (h_notJ_le 4 (hJ_false h4) y)
      (h_edge_le y _ _ hw0v) (h_edge_le y _ _ hw04.symm) (h_edge_le y _ _ hw01.symm)
      (h_edge_le y _ _ hw1v) (h_edge_le y _ _ hw10.symm) (h_edge_le y _ _ hw12.symm)
      (h_edge_le y _ _ hw2v) (h_edge_le y _ _ hw21.symm) (h_edge_le y _ _ hw23.symm)
  · -- Case 6: J = {0, 1, 3}, K = {3}; S = 14, M = 5, SLACK at y = a 0
    obtain ⟨w0, hw0v, hw04, hw01⟩ := hJ_true h0
    obtain ⟨w1, hw1v, hw10, hw12⟩ := hJ_true h1
    obtain ⟨w3, hw3v, hw32, hw34⟩ := hJ_true h3
    obtain ⟨z3, hz3v, hz3a⟩ := hz_ex 3
    refine weighted_list_contra M hdeg
      [(a 0, 1), (a 1, 1), (a 2, 1), (a 3, 2), (a 4, 1), (v, 3), (w0, 1), (w1, 1), (w3, 1), (z3, 2)] 14 5
      rfl (fun y => ?_) (Or.inr ⟨by decide, a 0, ?_⟩)
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
      exact cap_case5 (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _)
        (h_edge_le y _ _ ha01) (h_edge_le y _ _ ha12) (h_edge_le y _ _ ha23) (h_edge_le y _ _ ha34) (h_edge_le y _ _ ha40)
        (h_notJ_le 2 (hJ_false h2) y) (h_notJ_le 4 (hJ_false h4) y)
        (h_edge_le y _ _ hw0v) (h_edge_le y _ _ hw04.symm) (h_edge_le y _ _ hw01.symm)
        (h_edge_le y _ _ hw1v) (h_edge_le y _ _ hw10.symm) (h_edge_le y _ _ hw12.symm)
        (h_edge_le y _ _ hw3v) (h_edge_le y _ _ hw32.symm) (h_edge_le y _ _ hw34.symm)
        (h_edge_le y _ _ hz3v) (h_edge_le y _ _ hz3a.symm)
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
      have hna02 : ¬ M.Adj (a 0) (a 2) := fun h =>
        OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hMTF ha01 ha12 h
      have hna03 : ¬ M.Adj (a 0) (a 3) := fun h =>
        OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hMTF h ha34 ha40.symm
      have hna0v : ¬ M.Adj (a 0) v := fun h => hv_a 0 h.symm
      have hna0w0 : ¬ M.Adj (a 0) w0 := fun h =>
        OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hMTF ha01 hw01.symm h
      have hna0w3 : ¬ M.Adj (a 0) w3 := fun h =>
        OMA.R_Erdos128_erdos_128_R2.not_adj_of_cliqueFree_three hMTF ha40.symm hw34.symm h
      have hna0z3 : ¬ M.Adj (a 0) z3 := fun h => (hJ_false h4) ⟨z3, hz3v, hz3a, h.symm⟩
      have hw10' : M.Adj (a 0) w1 := hw10.symm
      simp only [M.loopless.irrefl (a 0), ha01, hna02, hna03, ha40.symm, hna0v, hna0w0,
        hw10', hna0w3, hna0z3, ite_false, ite_true]
      decide
  · -- Case 7: J = {0, 1, 2, 3}, K = ∅; S = 17, M = 6
    obtain ⟨w0, hw0v, hw04, hw01⟩ := hJ_true h0
    obtain ⟨w1, hw1v, hw10, hw12⟩ := hJ_true h1
    obtain ⟨w2, hw2v, hw21, hw23⟩ := hJ_true h2
    obtain ⟨w3, hw3v, hw32, hw34⟩ := hJ_true h3
    refine weighted_list_contra M hdeg
      [(a 0, 2), (a 1, 1), (a 2, 1), (a 3, 2), (a 4, 2), (v, 3), (w0, 1), (w1, 2), (w2, 2), (w3, 1)] 17 6
      rfl (fun y => ?_) (Or.inl ⟨hn_pos, by decide⟩)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    exact cap_case6 (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _)
      (h_edge_le y _ _ ha01) (h_edge_le y _ _ ha12) (h_edge_le y _ _ ha23) (h_edge_le y _ _ ha34) (h_edge_le y _ _ ha40)
      (h_notJ_le 4 (hJ_false h4) y)
      (h_edge_le y _ _ hw0v) (h_edge_le y _ _ hw04.symm) (h_edge_le y _ _ hw01.symm)
      (h_edge_le y _ _ hw1v) (h_edge_le y _ _ hw10.symm) (h_edge_le y _ _ hw12.symm)
      (h_edge_le y _ _ hw2v) (h_edge_le y _ _ hw21.symm) (h_edge_le y _ _ hw23.symm)
      (h_edge_le y _ _ hw3v) (h_edge_le y _ _ hw32.symm) (h_edge_le y _ _ hw34.symm)
  · -- Case 8: J = {0, 1, 2, 3, 4} (Grötzsch); S = 29, M = 10
    obtain ⟨w0, hw0v, hw04, hw01⟩ := hJ_true h0
    obtain ⟨w1, hw1v, hw10, hw12⟩ := hJ_true h1
    obtain ⟨w2, hw2v, hw21, hw23⟩ := hJ_true h2
    obtain ⟨w3, hw3v, hw32, hw34⟩ := hJ_true h3
    obtain ⟨w4, hw4v, hw43, hw40⟩ := hJ_true h4
    refine weighted_list_contra M hdeg
      [(a 0, 3), (a 1, 3), (a 2, 3), (a 3, 3), (a 4, 3), (v, 4),
       (w0, 2), (w1, 2), (w2, 2), (w3, 2), (w4, 2)] 29 10
      rfl (fun y => ?_) (Or.inl ⟨hn_pos, by decide⟩)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact cap_case7 (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _) (ite_one_le _)
      (h_edge_le y _ _ ha01) (h_edge_le y _ _ ha12) (h_edge_le y _ _ ha23) (h_edge_le y _ _ ha34) (h_edge_le y _ _ ha40)
      (h_edge_le y _ _ hw0v) (h_edge_le y _ _ hw04.symm) (h_edge_le y _ _ hw01.symm)
      (h_edge_le y _ _ hw1v) (h_edge_le y _ _ hw10.symm) (h_edge_le y _ _ hw12.symm)
      (h_edge_le y _ _ hw2v) (h_edge_le y _ _ hw21.symm) (h_edge_le y _ _ hw23.symm)
      (h_edge_le y _ _ hw3v) (h_edge_le y _ _ hw32.symm) (h_edge_le y _ _ hw34.symm)
      (h_edge_le y _ _ hw4v) (h_edge_le y _ _ hw43.symm) (h_edge_le y _ _ hw40.symm)

end Erdos128R2H1

theorem OMA.solution : OMA.R_Erdos128_erdos_128_R2.H1 := by
  intro V _ G _ _ _ _ _ _ _ hnot3 h14 _ _ hTF
  exact hnot3 (Erdos128R2H1.colorable_three_of_fourteen_fifths G hTF h14)
