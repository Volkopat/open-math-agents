import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H1_R1

/-!
# Carries in the second column of a Pascal row

Write `B = 2^a`, `n = B-c`, and divide `c(c+1)` by `B` with quotient `q`
and remainder `r`. The high and low blocks of `n(n-1)` are then
`B-1-(2c-q)` and `r`. Complementation in the high block gives an exact
weight formula for column two for every positive carry.

For a single carry the formula simplifies further. The first two columns
have opposite weight parity precisely when `c(c+1)` has odd weight.
Moreover `a` is determined by `c` in this range.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H1_R1_H1_R1

open OMA.R_OeisA249609_conjecture_R1_H2_R1_H1_R1

/-- Removing the final zero from the doubled coefficient and complementing
the high block computes the weight without a binomial coefficient. -/
theorem second_weight {a c n q r : ℕ} (hn : n+c = 2^a) (hc : 0<c)
    (hsize : 2*c ≤ 2^a) (hq : 0<q) (hqle : q ≤ 2*c)
    (hs : r + 2^a*q = c*(c+1)) (hr : r < 2^a) :
    (Nat.digits 2 (n.choose 2)).count 1 + (Nat.digits 2 (2*c-q)).count 1 =
      a + (Nat.digits 2 r).count 1 := by
  let z := 2^a - 1 - (2*c-q)
  have hz : z + (2*c-q) + 1 = 2^a := by dsimp [z]; omega
  have hz' : z + 2*c + 1 = 2^a + q := by omega
  have hn' : n-1+1 = n := by omega
  have product : n*(n-1) = z*2^a+r := by
    rw [← hn] at hz' hs ⊢
    nlinarith only [congrArg (fun t => t*n) hn',
      congrArg (fun t => t*(n+c)) hz', hs]
  have twice : 2*n.choose 2 = n*(n-1) := by
    simpa [Nat.descFactorial, mul_comm] using
      (Nat.descFactorial_eq_factorial_mul_choose n 2).symm
  have blocks := count_ones_append z a r hr
  rw [← product, ← twice, even_digits_double] at blocks
  have high := complement a z (2*c-q) hz
  omega

/-- The remaining single-carry rows, parametrized by the defect alone. -/
def H1 : Prop := ∀ c : ℕ, 1 < c → Odd c →
  let n := 2 ^ Nat.log 2 (c*(c+1)) - c
  OeisA249609.isEvil (c*(c+1)) = true → OeisA249609.isEvil n = false →
  ∃ k ∈ List.range' 1 n, OeisA249609.isEvil (n.choose k) = true

/-- The remaining rows with a carry of at least two. All three weights in
the parity restriction are computed from the defect and the block size. -/
def H2 : Prop := ∀ e c : ℕ, 1 < c → c ≤ 2^e → Odd c →
  let b := 2^(e+1)
  let q := c*(c+1)/b
  let r := c*(c+1)%b
  let w := fun x : ℕ => (Nat.digits 2 x).count 1
  2 ≤ q → (w (2*c-q) + w (c-1) + w r) % 2 = 0 →
  OeisA249609.isEvil (b-c) = false →
  ∃ k ∈ List.range' 1 (b-c), OeisA249609.isEvil ((b-c).choose k) = true

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H1_R1.H1 := by
  intro single multiple e c hc hcBound hcOdd hlarge hfirst
  let b := 2^(e+1)
  let weight (x : ℕ) := (Nat.digits 2 x).count 1
  let n := b-c
  let q := c*(c+1)/b
  let r := c*(c+1)%b
  change OeisA249609.isEvil n = false at hfirst
  change ∃ k ∈ List.range' 1 n, OeisA249609.isEvil (n.choose k) = true
  have hsize : 2*c ≤ b := by dsimp [b]; rw [pow_succ]; omega
  have hn : n+c=b := by dsimp [n]; omega
  have hb : 0<b := by dsimp [b]; positivity
  have hq : 0<q := Nat.div_pos hlarge hb
  have hqle : q ≤ c := calc
    q ≤ c*b/b := Nat.div_le_div_right (Nat.mul_le_mul_left c (by omega))
    _ = c := Nat.mul_div_cancel _ hb
  have hs : r+b*q=c*(c+1) := Nat.mod_add_div _ _
  have hr : r<b := Nat.mod_lt _ hb
  have hsecond := second_weight (a := e+1) hn (by omega) hsize hq (by omega) hs hr
  change weight (n.choose 2) + weight (2*c-q) = e+1 + weight r at hsecond
  have hcomp : weight n + weight (c-1) = e+1 :=
    complement _ _ _ (by change n+(c-1)+1=b; omega)
  by_cases hit : weight (n.choose 2) % 2 = 0
  · exact ⟨2, List.mem_range'_1.mpr ⟨by decide, by omega⟩,
      by simpa only [weight, OeisA249609.isEvil, beq_iff_eq] using hit⟩
  have hodd : weight n % 2 ≠ 0 := by simpa [OeisA249609.isEvil, weight] using hfirst
  by_cases one : q = 1
  · rw [one, Nat.mul_one] at hs
    rw [one] at hsecond
    have hlow : weight (2*c-1) = weight (c-1) + 1 := by
      have h := count_ones_append (c-1) 1 1 (by decide)
      rw [show (c-1)*2^1+1 = 2*c-1 by omega] at h
      exact h
    have hprod : weight (c*(c+1)) = 1 + weight r := by
      have h := count_ones_append 1 (e+1) r hr
      rw [Nat.one_mul, ← Nat.add_comm r, hs] at h
      exact h
    have hevil : OeisA249609.isEvil (c*(c+1)) = true := by
      change (weight (c*(c+1)) % 2 == 0) = true
      rw [beq_iff_eq]
      omega
    have hlog : Nat.log 2 (c*(c+1)) = e+1 :=
      Nat.log_eq_of_pow_le_of_lt_pow hlarge (by rw [pow_succ]; change c*(c+1)<b*2; omega)
    have H := single c hc hcOdd
    dsimp only at H
    rw [hlog] at H
    exact H hevil hfirst
  · exact multiple e c hc hcBound hcOdd (by change 2≤q; omega)
      (by change (weight (2*c-q) + weight (c-1) + weight r) % 2 = 0; omega) hfirst

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H1_R1_H1_R1
