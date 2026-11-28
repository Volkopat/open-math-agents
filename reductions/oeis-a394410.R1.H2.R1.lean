import OMAReductions.R_oeis_a394410_R1
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.Ring


/-! Quadratic reciprocity strengthens the factor progression for a prime
base congruent to one modulo four. -/

namespace OMA.Oeis394410Reciprocity

theorem even_multiplier {p q k : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hq : q.Prime) (heq : q = 2 * p * k + 1) (hdiv : q ∣ p ^ p + 1) :
    Even k := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact q.Prime := ⟨hq⟩
  have heq' : q = 2 * (p * k) + 1 := by rw [heq, mul_assoc]
  have hqgt : 2 < q := by
    have hq2 := hq.two_le
    omega
  have hqCast : ((q : ℤ) : ZMod p) = 1 := by
    push_cast
    rw [heq]
    push_cast
    simp
  have hleg : legendreSym q (p : ℤ) = 1 := by
    rw [legendreSym.quadratic_reciprocity_one_mod_four hp4 hqgt.ne', legendreSym, hqCast]
    simp
  have hzero : ((p ^ p + 1 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  push_cast at hzero
  have hbase : (p : ZMod q) ^ p = -1 := by
    calc
      _ = (p : ZMod q) ^ p + 1 - 1 := by ring
      _ = _ := by rw [hzero, zero_sub]
  have hhalf : q / 2 = p * k := by omega
  have heuler := legendreSym.eq_pow q (p : ℤ)
  simp only [hleg, Int.cast_one, Int.cast_natCast, hhalf, pow_mul, hbase] at heuler
  by_contra hk
  have hkodd := Nat.not_even_iff_odd.mp hk
  rw [hkodd.neg_one_pow] at heuler
  have htwo : ((2 : ℕ) : ZMod q) = 0 := by
    have hadd := congrArg (fun x : ZMod q => 1 + x) heuler
    simpa [one_add_one_eq_two] using hadd
  have hqd := (ZMod.natCast_eq_zero_iff 2 q).mp htwo
  exact (Nat.le_of_dvd (by decide) hqd).not_gt hqgt

end OMA.Oeis394410Reciprocity


/-! Residues of the exact quadratic recurrence modulo eight. -/

namespace OMA.Oeis394410Residues

open OMA.S_oeis_a394410

private theorem square_mod16 (x : ℕ) : x^2 % 16 = (x%8)^2 % 16 := by
  let r := x%8
  let q := x/8
  have hx : r+8*q = x := Nat.mod_add_div x 8
  have hsq : x^2 = r^2+16*(r*q+4*q^2) := by rw [← hx]; ring
  rw [hsq]
  change (r^2+16*(r*q+4*q^2)) % 16 = r^2 % 16
  omega

private theorem next_mod8 (x y : ℕ) :
    ((x^2+y^2)/2)%8 = (((x%8)^2%16 + (y%8)^2%16)%16)/2 := by
  have h (m : ℕ) : (m/2)%8 = (m%16)/2 := by omega
  rw [h, Nat.add_mod (x^2) (y^2) 16, square_mod16 x, square_mod16 y]

/-- Consecutive blocks starting at `4` have residues `1,5,5`. -/
theorem mod_eight_blocks (k : ℕ) :
    a (3*k+4)%8 = 1 ∧ a (3*k+5)%8 = 5 ∧ a (3*k+6)%8 = 5 := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    have h1 : a (3*k+7)%8 = 1 := by
      change ((a (3*k+6)^2 + a (3*k+5)^2)/2)%8 = 1
      rw [next_mod8, ih.2.2, ih.2.1]
      rfl
    have h2 : a (3*k+8)%8 = 5 := by
      change ((a (3*k+7)^2 + a (3*k+6)^2)/2)%8 = 5
      rw [next_mod8, h1, ih.2.2]
      rfl
    have h3 : a (3*k+9)%8 = 5 := by
      change ((a (3*k+8)^2 + a (3*k+7)^2)/2)%8 = 5
      rw [next_mod8, h2, h1]
      rfl
    rw [show 3*(k+1)+4 = 3*k+7 by omega, show 3*(k+1)+5 = 3*k+8 by omega,
      show 3*(k+1)+6 = 3*k+9 by omega]
    exact ⟨h1, h2, h3⟩

/-- The sequence has a three-term residue cycle on all indices from four. -/
theorem mod_eight (n : ℕ) (hn : 4 ≤ n) : a n % 8 = if n%3 = 1 then 1 else 5 := by
  let k := (n-4)/3
  have h : n = 3*k+4 ∨ n = 3*k+5 ∨ n = 3*k+6 := by dsimp [k]; omega
  have h4 : (3*k+4)%3 = 1 := by omega
  have h5 : (3*k+5)%3 ≠ 1 := by omega
  have h6 : (3*k+6)%3 ≠ 1 := by omega
  rcases h with h | h | h
  · rw [h, if_pos h4]
    exact (mod_eight_blocks k).1
  · rw [h, if_neg h5]
    exact (mod_eight_blocks k).2.1
  · rw [h, if_neg h6]
    exact (mod_eight_blocks k).2.2

theorem mod_four (n : ℕ) (hn : 4 ≤ n) : a n % 4 = 1 := by
  have h : a n % 4 = (a n % 8) % 4 := by omega
  rw [h, mod_eight n hn]
  split <;> rfl

end OMA.Oeis394410Residues

namespace OMA.Oeis394410Reciprocity

open OMA.S_oeis_a394410

theorem residue_mod8_cases (n : ℕ) (hn : 4 ≤ n) : a n % 8 = 1 ∨ a n % 8 = 5 := by
  rw [Oeis394410Residues.mod_eight n hn]
  split <;> simp

end OMA.Oeis394410Reciprocity


/-! Reduce the progression test to prime divisors that are one modulo four
times the base, splitting by the two actual residues of the base modulo eight. -/

namespace OMA.R_oeis_a394410_R1_H2_R1

open OMA.S_oeis_a394410 OMA.Oeis394410Reciprocity

/-- The candidate divisors for bases congruent to one modulo eight. -/
def H1 : Prop := ∀ n : ℕ, 11 ≤ n → (a n).Prime → a n % 8 = 1 →
  let p := a n
  ∀ j : ℕ, 0 < j → let q := 4 * p * j + 1
    q.Prime → q ^ 2 ≤ (p ^ p + 1) / (p + 1) → ¬q ∣ p ^ p + 1

/-- The candidate divisors for bases congruent to five modulo eight. -/
def H2 : Prop := ∀ n : ℕ, 11 ≤ n → (a n).Prime → a n % 8 = 5 →
  let p := a n
  ∀ j : ℕ, 0 < j → let q := 4 * p * j + 1
    q.Prime → q ^ 2 ≤ (p ^ p + 1) / (p + 1) → ¬q ∣ p ^ p + 1

theorem main : H1 → H2 → OMA.R_oeis_a394410_R1.H2 := by
  intro h1 h2 n hn hp
  dsimp only
  intro k hq hle hdiv
  have hmod := residue_mod8_cases n (by omega)
  have hp4 := OMA.Oeis394410Residues.mod_four n (by omega)
  obtain ⟨j, hj⟩ := even_multiplier hp hp4 hq rfl hdiv
  have heq : 2 * a n * k + 1 = 4 * a n * j + 1 := by
    rw [hj]
    ring
  rw [heq] at hq hle hdiv
  have hjpos : 0 < j := by
    by_contra! hh
    have hj0 : j = 0 := by omega
    exact Nat.not_prime_one (by simpa [hj0] using hq)
  rcases hmod with hm | hm
  · exact h1 n hn hp hm j hjpos hq hle hdiv
  · exact h2 n hn hp hm j hjpos hq hle hdiv

end OMA.R_oeis_a394410_R1_H2_R1
