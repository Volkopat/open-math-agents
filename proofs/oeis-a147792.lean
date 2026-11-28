import OMAStatements.S_oeis_a147792

/-!
R. J. Mathar conjectured the recurrence in OEIS A147792 in 2008. After
reducing the defining fraction, the denominator at index n is a quadratic
in n times a factor depending only on n modulo eight. Substitution into
the recurrence gives a polynomial identity on each residue class.
-/

namespace BrackettDenominator

open OMA.S_oeis_a147792

private theorem value (n : ℕ) :
    a n = (16 / Nat.gcd 16 (n * (n + 2))) * (n + 1) ^ 2 := by
  let t := n * (n + 2)
  have fraction : (1 : ℚ) / 16 - 1 / ((4 * n + 4 : ℕ) : ℚ) ^ 2 =
      mkRat (t : ℤ) (16 * (t + 1)) := by
    rw [Rat.mkRat_eq_div]
    dsimp [t]
    push_cast
    field_simp
    ring
  change ((1 : ℚ) / 16 - 1 / ((4 * n + 4 : ℕ) : ℚ) ^ 2).den = _
  rw [fraction, Rat.den_mkRat, if_neg (by positivity)]
  simp only [Int.natAbs_natCast]
  have reduce : (16 * (t + 1)).gcd t = Nat.gcd 16 t := by
    rw [show 16 * (t + 1) = 16 + 16 * t by ring, Nat.gcd_add_mul_right_left]
  rw [reduce, Nat.mul_comm 16 (t + 1), Nat.mul_div_assoc _ (Nat.gcd_dvd_left 16 t),
    Nat.mul_comm (t + 1)]
  change (16 / Nat.gcd 16 t) * (t + 1) = (16 / Nat.gcd 16 t) * (n + 1)^2
  congr 1
  dsimp [t]
  ring

private theorem residue (q r : ℕ) :
    a (8 * q + r) = (16 / Nat.gcd 16 (r * (r + 2))) * (8 * q + r + 1)^2 := by
  rw [value, show (8 * q + r) * (8 * q + r + 2) =
    r * (r + 2) + 16 * (4 * q^2 + q * r + q) by ring,
    Nat.gcd_add_mul_left_right]

theorem result : type_of% @OMA.S_oeis_a147792.main := by
  intro n hn
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r < 8 ∧ n = 8 * q + (r + 18) :=
    ⟨(n - 18) / 8, (n - 18) % 8, Nat.mod_lt _ (by decide), by omega⟩
  simp only [
    show 8 * q + (r + 18) - 2 = 8 * q + (r + 16) by omega,
    show 8 * q + (r + 18) - 4 = 8 * q + (r + 14) by omega,
    show 8 * q + (r + 18) - 6 = 8 * q + (r + 12) by omega,
    show 8 * q + (r + 18) - 8 = 8 * q + (r + 10) by omega,
    show 8 * q + (r + 18) - 10 = 8 * q + (r + 8) by omega,
    show 8 * q + (r + 18) - 12 = 8 * q + (r + 6) by omega,
    show 8 * q + (r + 18) - 14 = 8 * q + (r + 4) by omega,
    show 8 * q + (r + 18) - 16 = 8 * q + (r + 2) by omega,
    show 8 * q + (r + 18) - 18 = 8 * q + r by omega]
  simp only [residue]
  interval_cases r <;> norm_num <;> ring

end BrackettDenominator

theorem OMA.solution : type_of% @OMA.S_oeis_a147792.main := BrackettDenominator.result
