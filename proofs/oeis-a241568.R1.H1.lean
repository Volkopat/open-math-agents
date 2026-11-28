import OMAReductions.R_oeis_a241568_R1

/-!
# Proof of `oeis-a241568.R1.H1`

For every prime `p > 3` outside the 24 residue classes where `p % 24 ∈ {1, 23}`,
`p % 5 ∈ {1, 4}`, and `p % 13 ∈ {1, 3, 4, 9, 10, 12}`, one of the Fibonacci numbers
`2, 3, 5, 13` lies in `[1, (p - 1) / 2]` and is a quadratic nonresidue modulo `p`.
Small primes `3 < p < 27` are handled explicitly, and primes `p ≥ 27` follow from
the second supplementary law and quadratic reciprocity for `2, 3, 5, 13`.
-/

-- Step oeis-a241568.R1.H1: hypothesis H1 of reduction oeis-a241568.R1
-- Credit: @lettucrisp

namespace OeisA241568H1

private lemma nat_cast_ne_zero_of_lt {p k : ℕ} (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    ((k : ℤ) : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt hk0 hkp

private lemma leg_eq_one_of_isSquare {p : ℕ} (k : ℕ) (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p)
    (hsq : IsSquare (k : ZMod p)) :
    @legendreSym p ⟨hp⟩ k = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [legendreSym.eq_one_iff p (nat_cast_ne_zero_of_lt hp hk0 hkp)]
  simpa using hsq

private lemma mod8_of_isSquare_two {p : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p)
    (hsq : IsSquare (2 : ZMod p)) : p % 8 = 1 ∨ p % 8 = 7 := by
  have : Fact p.Prime := ⟨hp⟩
  have hleg : legendreSym p 2 = 1 := by
    simpa using leg_eq_one_of_isSquare 2 hp (by omega) (by omega) hsq
  have hp2 : p ≠ 2 := by omega
  rw [legendreSym.at_two hp2] at hleg
  have hcast : (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := by
    rw [← ZMod.natCast_mod]
  rw [hcast] at hleg
  have hm : p % 8 < 8 := Nat.mod_lt p (by norm_num)
  interval_cases h : p % 8 <;> simp_all [ZMod.χ₈]

private lemma mod12_of_isSquare_three {p : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p)
    (hsq : IsSquare (3 : ZMod p)) : p % 12 = 1 ∨ p % 12 = 11 := by
  have hp2 : p ≠ 2 := by omega
  have hp_odd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hpow_sym : ((((-1 : ℤ) ^ ((p % 12 % 4) / 2)) : ℤ) : ZMod 3) =
      (((p % 12) % 3 : ℕ) : ZMod 3) ^ (3 / 2) := by
    have : Fact p.Prime := ⟨hp⟩
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hleg : legendreSym p 3 = 1 := by
      simpa using leg_eq_one_of_isSquare 3 hp (by omega) (by omega) hsq
    have hp3 : p ≠ 3 := by omega
    have hrec := legendreSym.quadratic_reciprocity hp2 (by decide : (3 : ℕ) ≠ 2) hp3
    norm_num at hrec
    rw [hleg, mul_one] at hrec
    have hs : ((legendreSym 3 (p : ℤ) : ℤ) : ZMod 3) = ((p : ZMod 3) ^ (3 / 2)) := by
      simpa using legendreSym.eq_pow 3 (p : ℤ)
    rw [hrec, ← ZMod.natCast_mod p 3] at hs
    have h3 : p % 3 = (p % 12) % 3 := by omega
    have hdiv2 : p / 2 = 2 * (p / 4) + (p % 12 % 4) / 2 := by omega
    have hpow : (-1 : ℤ) ^ (p / 2) = (-1 : ℤ) ^ ((p % 12 % 4) / 2) := by
      rw [hdiv2, pow_add, pow_mul]
      norm_num
    rw [hpow, h3] at hs
    exact hs
  have hm12 : p % 12 < 12 := Nat.mod_lt p (by norm_num)
  interval_cases h : p % 12
  all_goals first
    | (left; rfl)
    | (right; rfl)
    | omega
    | (exfalso; revert hpow_sym; decide)

private lemma mod5_of_isSquare_five {p : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p)
    (hsq : IsSquare (5 : ZMod p)) : p % 5 = 1 ∨ p % 5 = 4 := by
  have hpow_sym : (1 : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) ^ (5 / 2) := by
    have : Fact p.Prime := ⟨hp⟩
    have : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hleg : legendreSym p 5 = 1 := by
      simpa using leg_eq_one_of_isSquare 5 hp (by omega) (by omega) hsq
    have hp2 : p ≠ 2 := by omega
    have hrec := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p) (by decide) hp2
    norm_num at hrec
    rw [hleg] at hrec
    have hs : ((legendreSym 5 (p : ℤ) : ℤ) : ZMod 5) = ((p : ZMod 5) ^ (5 / 2)) := by
      simpa using legendreSym.eq_pow 5 (p : ℤ)
    rw [← hrec, ← ZMod.natCast_mod p 5] at hs
    simpa using hs
  have hm5 : p % 5 < 5 := Nat.mod_lt p (by norm_num)
  interval_cases h : p % 5
  all_goals first
    | (left; rfl)
    | (right; rfl)
    | (exfalso; revert hpow_sym; decide)

private lemma mod13_of_isSquare_thirteen {p : ℕ} (hp : p.Prime) (hp27 : 27 ≤ p)
    (hsq : IsSquare (13 : ZMod p)) : p % 13 ∈ ([1, 3, 4, 9, 10, 12] : List ℕ) := by
  have hpow_sym : (1 : ZMod 13) = ((p % 13 : ℕ) : ZMod 13) ^ (13 / 2) := by
    have : Fact p.Prime := ⟨hp⟩
    have : Fact (Nat.Prime 13) := ⟨by decide⟩
    have hleg : legendreSym p 13 = 1 := by
      simpa using leg_eq_one_of_isSquare 13 hp (by omega) (by omega) hsq
    have hp2 : p ≠ 2 := by omega
    have hrec := legendreSym.quadratic_reciprocity_one_mod_four (p := 13) (q := p) (by decide) hp2
    norm_num at hrec
    rw [hleg] at hrec
    have hs : ((legendreSym 13 (p : ℤ) : ℤ) : ZMod 13) = ((p : ZMod 13) ^ (13 / 2)) := by
      simpa using legendreSym.eq_pow 13 (p : ℤ)
    rw [← hrec, ← ZMod.natCast_mod p 13] at hs
    simpa using hs
  have hm13 : p % 13 < 13 := Nat.mod_lt p (by norm_num)
  interval_cases h : p % 13
  all_goals first | decide | (exfalso; revert hpow_sym; decide)

end OeisA241568H1

theorem OMA.solution : OMA.R_oeis_a241568_R1.H1 := by
  intro p hp hgt hnot
  by_cases hp27 : p < 27
  · interval_cases p
    all_goals first
      | (exfalso; exact absurd hp (by decide))
      | (refine ⟨2, by decide, by decide, ⟨3, by decide⟩, ?_⟩; rintro ⟨x, hx⟩; revert x hx; decide)
      | (refine ⟨3, by decide, by decide, ⟨4, by decide⟩, ?_⟩; rintro ⟨x, hx⟩; revert x hx; decide)
      | (refine ⟨5, by decide, by decide, ⟨5, by decide⟩, ?_⟩; rintro ⟨x, hx⟩; revert x hx; decide)
  · push Not at hp27
    by_cases h2 : IsSquare (2 : ZMod p)
    · by_cases h3 : IsSquare (3 : ZMod p)
      · by_cases h5 : IsSquare (5 : ZMod p)
        · by_cases h13 : IsSquare (13 : ZMod p)
          · exfalso
            have hm8 := OeisA241568H1.mod8_of_isSquare_two hp hp27 h2
            have hm12 := OeisA241568H1.mod12_of_isSquare_three hp hp27 h3
            have hm5 := OeisA241568H1.mod5_of_isSquare_five hp hp27 h5
            have hm13 := OeisA241568H1.mod13_of_isSquare_thirteen hp hp27 h13
            have hm24 : p % 24 = 1 ∨ p % 24 = 23 := by omega
            exact hnot ⟨hm24, hm5, hm13⟩
          · exact ⟨13, by omega, by omega, ⟨7, by decide⟩, h13⟩
        · exact ⟨5, by omega, by omega, ⟨5, by decide⟩, h5⟩
      · exact ⟨3, by omega, by omega, ⟨4, by decide⟩, h3⟩
    · exact ⟨2, by omega, by omega, ⟨3, by decide⟩, h2⟩
