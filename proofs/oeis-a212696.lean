import OMAStatements.S_oeis_a212696

namespace OMA.P212696

open OMA.S_oeis_a212696

lemma L1 (A B A' B' : ℕ) (hA : A' = A + 1) (hB : B' = B) :
    (Nat.choose A' B' : ℚ) * ((A' : ℚ) - (B' : ℚ)) = (A' : ℚ) * (Nat.choose A B : ℚ) := by
  rw [hA, hB]
  by_cases h : B ≤ A + 1
  · have h1 := Nat.choose_mul_succ_eq A B
    have q : (Nat.choose A B : ℚ) * ((A : ℚ) + 1)
        = (Nat.choose (A + 1) B : ℚ) * (((A + 1 - B : ℕ)) : ℚ) := by exact_mod_cast h1
    rw [Nat.cast_sub h] at q
    push_cast at q ⊢
    linear_combination -q
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma L2 (A B A' B' : ℕ) (hA : A' = A) (hB : B' = B + 1) :
    (Nat.choose A' B' : ℚ) * (B' : ℚ) = (Nat.choose A B : ℚ) * ((A : ℚ) - (B : ℚ)) := by
  rw [hA, hB]
  by_cases h : B ≤ A
  · have h1 := Nat.choose_succ_right_eq A B
    have q : (Nat.choose A (B + 1) : ℚ) * ((B : ℚ) + 1)
        = (Nat.choose A B : ℚ) * (((A - B : ℕ)) : ℚ) := by exact_mod_cast h1
    rw [Nat.cast_sub h] at q
    push_cast at q ⊢
    linear_combination q
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma L3 (A B A' B' : ℕ) (hA : A' = A + 1) (hB : B' = B + 1) :
    (Nat.choose A' B' : ℚ) * (B' : ℚ) = (A' : ℚ) * (Nat.choose A B : ℚ) := by
  rw [hA, hB]
  have h1 := Nat.add_one_mul_choose_eq A B
  have q : ((A : ℚ) + 1) * (Nat.choose A B : ℚ)
      = (Nat.choose (A + 1) (B + 1) : ℚ) * ((B : ℚ) + 1) := by exact_mod_cast h1
  push_cast at q ⊢
  linear_combination -q

namespace R1



/-- The summand, as a rational number. -/
def T (N k : ℕ) : ℚ :=
  ((1 / ((1 : ℚ) + ((2 : ℚ) * (N : ℚ)))) * ((1 : ℚ) + (N : ℚ))) * (Nat.choose (N + 2 * k) (N + k) : ℚ) * (Nat.choose (2 * N + 1) (N + k + 1) : ℚ) * (-1 : ℚ) ^ (N + k)

/-- The telescoping certificate. -/
def G (m k : ℕ) : ℚ :=
  ((-1 : ℚ) * (k : ℚ) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ)) * ((-28440 : ℚ) + ((-150884 : ℚ) * (m : ℚ) ^ 2) + ((-120360 : ℚ) * (m : ℚ) ^ 3) + ((-101844 : ℚ) * (m : ℚ)) + ((-56020 : ℚ) * (m : ℚ) ^ 4) + ((-45612 : ℚ) * (k : ℚ)) + ((-15256 : ℚ) * (m : ℚ) ^ 5) + ((-10692 : ℚ) * (k : ℚ) ^ 2) + ((-2820 : ℚ) * (k : ℚ) ^ 3) + ((-2256 : ℚ) * (m : ℚ) ^ 6) + ((-216 : ℚ) * (k : ℚ) ^ 4) + ((-140 : ℚ) * (m : ℚ) ^ 7) + ((36 : ℚ) * (k : ℚ) ^ 6) + ((192 : ℚ) * (k : ℚ) ^ 5) + ((-141239 : ℚ) * (k : ℚ) * (m : ℚ) ^ 2) + ((-125656 : ℚ) * (k : ℚ) * (m : ℚ)) + ((-83061 : ℚ) * (k : ℚ) * (m : ℚ) ^ 3) + ((-26983 : ℚ) * (k : ℚ) * (m : ℚ) ^ 4) + ((-25567 : ℚ) * (m : ℚ) * (k : ℚ) ^ 2) + ((-23473 : ℚ) * (k : ℚ) ^ 2 * (m : ℚ) ^ 2) + ((-10339 : ℚ) * (k : ℚ) ^ 2 * (m : ℚ) ^ 3) + ((-4593 : ℚ) * (k : ℚ) * (m : ℚ) ^ 5) + ((-4552 : ℚ) * (m : ℚ) * (k : ℚ) ^ 3) + ((-2488 : ℚ) * (k : ℚ) ^ 3 * (m : ℚ) ^ 2) + ((-2180 : ℚ) * (k : ℚ) ^ 2 * (m : ℚ) ^ 4) + ((-510 : ℚ) * (k : ℚ) ^ 3 * (m : ℚ) ^ 3) + ((-320 : ℚ) * (k : ℚ) * (m : ℚ) ^ 6) + ((-175 : ℚ) * (k : ℚ) ^ 2 * (m : ℚ) ^ 5) + ((-25 : ℚ) * (k : ℚ) ^ 3 * (m : ℚ) ^ 4) + ((15 : ℚ) * (m : ℚ) * (k : ℚ) ^ 6) + ((16 : ℚ) * (m : ℚ) * (k : ℚ) ^ 4) + ((50 : ℚ) * (k : ℚ) ^ 4 * (m : ℚ) ^ 3) + ((55 : ℚ) * (k : ℚ) ^ 5 * (m : ℚ) ^ 2) + ((165 : ℚ) * (k : ℚ) ^ 4 * (m : ℚ) ^ 2) + ((212 : ℚ) * (m : ℚ) * (k : ℚ) ^ 5))) / ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((1 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))))
    * ((Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) * (-1 : ℚ) ^ (m + k))

set_option maxHeartbeats 4000000 in
lemma pt (m k : ℕ) :
    ((36 : ℚ) * ((1 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((12 : ℚ) + ((5 : ℚ) * (m : ℚ)))) * T (m) k + ((-4 : ℚ) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((186 : ℚ) + ((5 : ℚ) * (m : ℚ) ^ 3) + ((72 : ℚ) * (m : ℚ) ^ 2) + ((223 : ℚ) * (m : ℚ)))) * T (m + 1) k + ((-1 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((824 : ℚ) + ((115 : ℚ) * (m : ℚ) ^ 3) + ((691 : ℚ) * (m : ℚ) ^ 2) + ((1340 : ℚ) * (m : ℚ)))) * T (m + 2) k + ((2 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((5 : ℚ) * (m : ℚ)))) * T (m + 3) k
      = G m (k + 1) - G m k := by
  have he1 := L3 ((m + 2) + 2 * k) ((m + 2) + k) (m + 2 * k + 3) (m + k + 3) (by ring) (by ring)
  push_cast at he1
  have me1 : (Nat.choose ((m + 2) + 2 * k) ((m + 2) + k) : ℚ) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) = ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) := by
    linear_combination ((-1 : ℚ)) * he1
  have me1c : (Nat.choose ((m + 2) + 2 * k) ((m + 2) + k) : ℚ) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) = ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) := by
    have hx : ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) * me1
  have e1 : (Nat.choose ((m + 2) + 2 * k) ((m + 2) + k) : ℚ) = ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) / ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) := by
    have hx : ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me1c
  have he2 := L3 ((m + 1) + 2 * k) ((m + 1) + k) ((m + 2) + 2 * k) ((m + 2) + k) (by ring) (by ring)
  push_cast at he2
  have me2 : (Nat.choose ((m + 1) + 2 * k) ((m + 1) + k) : ℚ) * (((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) = (((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) := by
    linear_combination (((-3 : ℚ) + ((-1 : ℚ) * (m : ℚ)) + ((-2 : ℚ) * (k : ℚ)))) * he2 + (((2 : ℚ) + (k : ℚ) + (m : ℚ))) * me1c
  have me2c : (Nat.choose ((m + 1) + 2 * k) ((m + 1) + k) : ℚ) * (((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) = (((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) := by
    have hx : (((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination ((((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))))) * me2
  have e2 : (Nat.choose ((m + 1) + 2 * k) ((m + 1) + k) : ℚ) = (((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) / (((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) := by
    have hx : (((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me2c
  have he3 := L3 (m + 2 * k) (m + k) ((m + 1) + 2 * k) ((m + 1) + k) (by ring) (by ring)
  push_cast at he3
  have me3 : (Nat.choose (m + 2 * k) (m + k) : ℚ) * (((1 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) = (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) := by
    linear_combination (((-1 : ℚ) * ((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))))) * he3 + (((1 : ℚ) + (k : ℚ) + (m : ℚ))) * me2c
  have me3c : (Nat.choose (m + 2 * k) (m + k) : ℚ) * (((1 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) = (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) := by
    have hx : (((1 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination ((((1 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))))) * me3
  have e3 : (Nat.choose (m + 2 * k) (m + k) : ℚ) = (((1 : ℚ) + (k : ℚ) + (m : ℚ)) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) / (((1 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) := by
    have hx : (((1 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me3c
  have he4 := L1 (m + 2 * k + 3) (m + k + 3) (m + 2 * k + 4) (m + k + 3) (by ring) (by ring)
  push_cast at he4
  have me4 : (Nat.choose (m + 2 * k + 4) (m + k + 3) : ℚ) * ((1 : ℚ) + (k : ℚ)) = ((4 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) := by
    linear_combination ((1 : ℚ)) * he4
  have me4c : (Nat.choose (m + 2 * k + 4) (m + k + 3) : ℚ) * ((1 : ℚ) + (k : ℚ)) = ((4 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) := by
    have hx : ((1 : ℚ) + (k : ℚ)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((1 : ℚ) + (k : ℚ))) * me4
  have he5 := L3 (m + 2 * k + 4) (m + k + 3) (m + 2 * (k + 1) + 3) (m + (k + 1) + 3) (by ring) (by ring)
  push_cast at he5
  have me5 : (Nat.choose (m + 2 * (k + 1) + 3) (m + (k + 1) + 3) : ℚ) * (((1 : ℚ) + (k : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) = (((4 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((5 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) := by
    linear_combination (((1 : ℚ) + (k : ℚ))) * he5 + (((5 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) * me4c
  have me5c : (Nat.choose (m + 2 * (k + 1) + 3) (m + (k + 1) + 3) : ℚ) * (((1 : ℚ) + (k : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) = (((4 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((5 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) := by
    have hx : (((1 : ℚ) + (k : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination ((((1 : ℚ) + (k : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ)))) * me5
  have e5 : (Nat.choose (m + 2 * (k + 1) + 3) (m + (k + 1) + 3) : ℚ) = (((4 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) * ((5 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ)))) * (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) / (((1 : ℚ) + (k : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) := by
    have hx : (((1 : ℚ) + (k : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me5c
  have e6 : (Nat.choose ((m + 3) + 2 * k) ((m + 3) + k) : ℚ) = (Nat.choose (m + 2 * k + 3) (m + k + 3) : ℚ) := by
    rw [show (m + 3) + 2 * k = m + 2 * k + 3 from by ring]
    rw [show (m + 3) + k = m + k + 3 from by ring]
  have he7 := L1 (2 * m + 6) (m + k + 4) (2 * m + 7) (m + k + 4) (by ring) (by ring)
  push_cast at he7
  have me7 : (Nat.choose (2 * m + 6) (m + k + 4) : ℚ) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))) = ((3 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    linear_combination ((-1 : ℚ)) * he7
  have me7c : (Nat.choose (2 * m + 6) (m + k + 4) : ℚ) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))) = ((3 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    have hx : ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) * me7
  have he8 := L1 (2 * m + 5) (m + k + 4) (2 * m + 6) (m + k + 4) (by ring) (by ring)
  push_cast at he8
  have me8 : (Nat.choose (2 * m + 5) (m + k + 4) : ℚ) * ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = (((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    linear_combination (((-7 : ℚ) + ((-2 : ℚ) * (m : ℚ)))) * he8 + (((2 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ)))) * me7c
  have me8c : (Nat.choose (2 * m + 5) (m + k + 4) : ℚ) * ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = (((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    have hx : ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * me8
  have he9 := L1 (2 * m + 4) (m + k + 4) (2 * m + 5) (m + k + 4) (by ring) (by ring)
  push_cast at he9
  have me9 : (Nat.choose (2 * m + 4) (m + k + 4) : ℚ) * ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    linear_combination (((-2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * he9 + (((1 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ)))) * me8c
  have me9c : (Nat.choose (2 * m + 4) (m + k + 4) : ℚ) * ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ)))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    have hx : ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * me9
  have he10 := L3 (2 * m + 3) (m + k + 3) (2 * m + 4) (m + k + 4) (by ring) (by ring)
  push_cast at he10
  have me10 : (Nat.choose (2 * m + 3) (m + k + 3) : ℚ) * ((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    linear_combination (((-2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * he10 + (((4 : ℚ) + (k : ℚ) + (m : ℚ))) * me9c
  have me10c : (Nat.choose (2 * m + 3) (m + k + 3) : ℚ) * ((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    have hx : ((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * me10
  have he11 := L3 (2 * m + 2) (m + k + 2) (2 * m + 3) (m + k + 3) (by ring) (by ring)
  push_cast at he11
  have me11 : (Nat.choose (2 * m + 2) (m + k + 2) : ℚ) * ((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    linear_combination (((-4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * he11 + (((3 : ℚ) + (k : ℚ) + (m : ℚ))) * me10c
  have me11c : (Nat.choose (2 * m + 2) (m + k + 2) : ℚ) * ((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    have hx : ((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * me11
  have he12 := L3 (2 * m + 1) (m + k + 1) (2 * m + 2) (m + k + 2) (by ring) (by ring)
  push_cast at he12
  have me12 : (Nat.choose (2 * m + 1) (m + k + 1) : ℚ) * ((8 : ℚ) * ((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    linear_combination (((-4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * he12 + (((2 : ℚ) + (k : ℚ) + (m : ℚ))) * me11c
  have me12c : (Nat.choose (2 * m + 1) (m + k + 1) : ℚ) * ((8 : ℚ) * ((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    have hx : ((8 : ℚ) * ((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((8 : ℚ) * ((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * me12
  have e12 : (Nat.choose (2 * m + 1) (m + k + 1) : ℚ) = ((-1 : ℚ) * ((-1 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((2 : ℚ) + (k : ℚ) + (m : ℚ)) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) / ((8 : ℚ) * ((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) := by
    have hx : ((8 : ℚ) * ((1 : ℚ) + (m : ℚ)) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me12c
  have he13 := L3 (2 * m + 4) (m + k + 3) (2 * m + 5) (m + k + 4) (by ring) (by ring)
  push_cast at he13
  have me13 : (Nat.choose (2 * m + 4) (m + k + 3) : ℚ) * ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = (((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    linear_combination (((-2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * he13 + (((4 : ℚ) + (k : ℚ) + (m : ℚ))) * me8c
  have me13c : (Nat.choose (2 * m + 4) (m + k + 3) : ℚ) * ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = (((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    have hx : ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * me13
  have he14 := L3 (2 * (m + 1) + 1) ((m + 1) + k + 1) (2 * m + 4) (m + k + 3) (by ring) (by ring)
  push_cast at he14
  have me14 : (Nat.choose (2 * (m + 1) + 1) ((m + 1) + k + 1) : ℚ) * ((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = (((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    linear_combination (((-2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * he14 + (((3 : ℚ) + (k : ℚ) + (m : ℚ))) * me13c
  have me14c : (Nat.choose (2 * (m + 1) + 1) ((m + 1) + k + 1) : ℚ) * ((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = (((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    have hx : ((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * me14
  have e14 : (Nat.choose (2 * (m + 1) + 1) ((m + 1) + k + 1) : ℚ) = (((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((-2 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((3 : ℚ) + (k : ℚ) + (m : ℚ)) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) / ((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) := by
    have hx : ((4 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me14c
  have he15 := L3 (2 * (m + 2) + 1) ((m + 2) + k + 1) (2 * m + 6) (m + k + 4) (by ring) (by ring)
  push_cast at he15
  have me15 : (Nat.choose (2 * (m + 2) + 1) ((m + 2) + k + 1) : ℚ) * ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = ((-1 : ℚ) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    linear_combination (((-7 : ℚ) + ((-2 : ℚ) * (m : ℚ)))) * he15 + (((4 : ℚ) + (k : ℚ) + (m : ℚ))) * me7c
  have me15c : (Nat.choose (2 * (m + 2) + 1) ((m + 2) + k + 1) : ℚ) * ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) = ((-1 : ℚ) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    have hx : ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))))) * me15
  have e15 : (Nat.choose (2 * (m + 2) + 1) ((m + 2) + k + 1) : ℚ) = ((-1 : ℚ) * ((-3 : ℚ) + (k : ℚ) + ((-1 : ℚ) * (m : ℚ))) * ((4 : ℚ) + (k : ℚ) + (m : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) / ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) := by
    have hx : ((2 : ℚ) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ)))) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me15c
  have he16 := L2 (2 * m + 7) (m + k + 4) (2 * m + 7) (m + (k + 1) + 4) (by ring) (by ring)
  push_cast at he16
  have me16 : (Nat.choose (2 * m + 7) (m + (k + 1) + 4) : ℚ) * ((5 : ℚ) + (k : ℚ) + (m : ℚ)) = ((3 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    linear_combination ((1 : ℚ)) * he16
  have me16c : (Nat.choose (2 * m + 7) (m + (k + 1) + 4) : ℚ) * ((5 : ℚ) + (k : ℚ) + (m : ℚ)) = ((3 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    have hx : ((5 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
    apply mul_right_cancel₀ hx
    linear_combination (((5 : ℚ) + (k : ℚ) + (m : ℚ))) * me16
  have e16 : (Nat.choose (2 * m + 7) (m + (k + 1) + 4) : ℚ) = ((3 : ℚ) + (m : ℚ) + ((-1 : ℚ) * (k : ℚ))) * (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) / ((5 : ℚ) + (k : ℚ) + (m : ℚ)) := by
    have hx : ((5 : ℚ) + (k : ℚ) + (m : ℚ)) ≠ 0 := by positivity
    rw [eq_div_iff hx]
    exact me16c
  have e17 : (Nat.choose (2 * (m + 3) + 1) ((m + 3) + k + 1) : ℚ) = (Nat.choose (2 * m + 7) (m + k + 4) : ℚ) := by
    rw [show 2 * (m + 3) + 1 = 2 * m + 7 from by ring]
    rw [show (m + 3) + k + 1 = m + k + 4 from by ring]
  have hd0 : ((3 : ℚ) + (m : ℚ)) ≠ 0 := by positivity
  have hd1 : ((5 : ℚ) + ((2 : ℚ) * (m : ℚ))) ≠ 0 := by positivity
  have hd2 : ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))) ≠ 0 := by positivity
  have hd3 : ((1 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) ≠ 0 := by positivity
  have hd3b : ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) ≠ 0 := by positivity
  have hd4 : ((2 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) ≠ 0 := by positivity
  have hd4b : ((4 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) ≠ 0 := by positivity
  have hd5 : ((3 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) ≠ 0 := by positivity
  have hd5b : ((5 : ℚ) + (m : ℚ) + ((2 : ℚ) * (k : ℚ))) ≠ 0 := by positivity
  simp only [T, G]
  rw [e1, e2, e3, e5, e6, e12, e14, e15, e16, e17]
  push_cast
  field_simp
  ring

lemma aq (N : ℕ) : a (N) = ∑ k ∈ Finset.range (N + 1), T N k := by
  unfold a
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_range] at hk
  have e : ((-1 : ℚ)) ^ (N - k) = (-1) ^ (N + k) := by
    have h2 : N + k = (N - k) + 2 * k := by omega
    rw [h2, pow_add, pow_mul]
    norm_num
  rw [e, T]
  ring

lemma Tz (N k : ℕ) (h : N < k) : T N k = 0 := by
  have z : Nat.choose (2 * N + 1) (N + k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  unfold T
  rw [z]
  simp

lemma aqe (N M : ℕ) (h : N + 1 ≤ M) : a (N) = ∑ k ∈ Finset.range M, T N k := by
  rw [aq]
  apply Finset.sum_subset
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro x _ hx
    rw [Finset.mem_range] at hx
    exact Tz N x (by omega)

lemma G0 (m : ℕ) : G m 0 = 0 := by
  unfold G
  simp

lemma Gtop (m : ℕ) : G m (m + 3 + 1) = 0 := by
  have z : Nat.choose (2 * m + 7) (m + (m + 3 + 1) + 4) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  unfold G
  rw [z]
  simp

lemma recQ (m : ℕ) :
    ((36 : ℚ) * ((1 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((12 : ℚ) + ((5 : ℚ) * (m : ℚ)))) * a (m) + ((-4 : ℚ) * ((3 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((186 : ℚ) + ((5 : ℚ) * (m : ℚ) ^ 3) + ((72 : ℚ) * (m : ℚ) ^ 2) + ((223 : ℚ) * (m : ℚ)))) * a (m + 1) + ((-1 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((824 : ℚ) + ((115 : ℚ) * (m : ℚ) ^ 3) + ((691 : ℚ) * (m : ℚ) ^ 2) + ((1340 : ℚ) * (m : ℚ)))) * a (m + 2) + ((2 : ℚ) * ((2 : ℚ) + (m : ℚ)) * ((3 : ℚ) + (m : ℚ)) * ((7 : ℚ) + ((2 : ℚ) * (m : ℚ))) * ((7 : ℚ) + ((5 : ℚ) * (m : ℚ)))) * a (m + 3) = 0 := by
  have h := Finset.sum_congr (rfl : Finset.range (m + 3 + 1) = Finset.range (m + 3 + 1))
    (fun k _ => pt m k)
  rw [Finset.sum_range_sub, G0, Gtop] at h
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [aqe (m) (m + 3 + 1) (by omega), aqe (m + 1) (m + 3 + 1) (by omega), aqe (m + 2) (m + 3 + 1) (by omega), aqe (m + 3) (m + 3 + 1) (by omega)]
  linear_combination h

end R1

end OMA.P212696

open OMA.S_oeis_a212696 OMA.P212696 in
theorem OMA.solution : type_of% @OMA.S_oeis_a212696.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 1 = m + 2 := by omega
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e1, e2, e3]
  have r := R1.recQ m
  push_cast
  linear_combination r
