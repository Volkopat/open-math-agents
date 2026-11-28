import OMAStatements.S_oeis_a054723
import Mathlib

-- Reduction oeis-a054723.R2
-- Credit: @Pixelstorm44

/-!
# Cubic residues and factors of the form 6p + 1

Let q = 6p + 1 be prime, with p prime and p ≡ 1 mod 4. Then 2 is a square
modulo q. We show that q divides the Mersenne number exactly when 2 is also
a cube modulo q.

Putting x = 24n + 9 gives two cubics P = (x³ − 3)/6 and Q = x³ − 2.
Their simultaneous prime values supply exponents with the required divisor.
Both cubics are irreducible over the rationals by affine substitution in
X³ − 3 and X³ − 2, which are Eisenstein at 3 and 2 respectively.
The products at n = 0 and n = 1 are coprime, so every prime admits a
residue class avoiding both cubics. Infinitude of simultaneous prime
values is an open instance of Schinzel's hypothesis H.
-/

namespace OMA.R_oeis_a054723_R2

/-- Expanding the factor polynomial exhibits a cube root of 2 modulo its value. -/
theorem factor_add_two (n : ℕ) :
    6 * (2304*n^3 + 2592*n^2 + 972*n + 121) + 1 + 2 = (24*n + 9)^3 := by ring

/-- Each prime has a residue class where it divides neither polynomial. -/
theorem admissible (r : ℕ) (hr : r.Prime) :
    ∃ n : ℕ, let p := 2304*n^3 + 2592*n^2 + 972*n + 121
             ¬ r ∣ p * (6*p+1) := by
  by_contra! h
  have h0 : r ∣ 121 * 727 := Classical.not_not.mp (h 0)
  have h1 : r ∣ 5989 * 35935 := Classical.not_not.mp (h 1)
  have hd := Nat.dvd_gcd h0 h1
  have hg : Nat.gcd (121 * 727) (5989 * 35935) = 1 := by decide
  exact hr.not_dvd_one (hg ▸ hd)

/-- Cubic residue criterion for a prime candidate divisor. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 1 → (6 * p + 1).Prime →
    ((6 * p + 1) ∣ 2 ^ p - 1 ↔ ∃ x : ZMod (6 * p + 1), x ^ 3 = 2)

/-- Open simultaneous-prime-values problem for two admissible cubics. -/
def H2 : Prop :=
  {n : ℕ | let p := 2304*n^3 + 2592*n^2 + 972*n + 121
           p.Prime ∧ (6*p+1).Prime}.Infinite

theorem cubic_criterion : H1 := by
  intro p hp hp4 hq
  let q := 6 * p + 1
  change q.Prime at hq
  let _ : Fact q.Prime := ⟨hq⟩
  have hp2 := hp.two_le
  have hq2 : 2 < q := by dsimp [q]; omega
  have two_ne : (2 : ZMod q) ≠ 0 := by
    exact fun h => (Nat.not_dvd_of_pos_of_lt (by decide) hq2)
      ((ZMod.natCast_eq_zero_iff 2 q).mp h)
  have div_iff : q ∣ 2 ^ p - 1 ↔ (2 : ZMod q) ^ p = 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow,
      Nat.cast_two, Nat.cast_one, sub_eq_zero]
  rw [div_iff]
  constructor
  · intro h
    have hp3 : p % 3 ≠ 0 := by
      intro h0
      have he := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp
        (Nat.dvd_of_mod_eq_zero h0)
      omega
    by_cases hmod : p % 3 = 2
    · refine ⟨2 ^ ((p + 1) / 3), ?_⟩
      rw [← pow_mul, show (p + 1) / 3 * 3 = p + 1 by omega, pow_succ, h, one_mul]
    · refine ⟨2 ^ ((2 * p + 1) / 3), ?_⟩
      rw [← pow_mul, show (2 * p + 1) / 3 * 3 = p + p + 1 by omega, pow_succ,
        pow_add, h, one_mul, one_mul]
  · rintro ⟨x, hx⟩
    have hq8 : q % 8 = 7 := by dsimp [q]; omega
    obtain ⟨y, hy⟩ := (ZMod.exists_sq_eq_two_iff (by omega : q ≠ 2)).2 (Or.inr hq8)
    have hy2 : y ^ 2 = 2 := by rw [pow_two]; exact hy.symm
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx; exact two_ne hx.symm
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy2; exact two_ne hy2.symm
    have h2p : (2 : ZMod q) ^ (2 * p) = 1 := by
      rw [← hx, ← pow_mul, show 3 * (2 * p) = q - 1 by dsimp [q]; omega]
      exact ZMod.pow_card_sub_one_eq_one hx0
    have h3p : (2 : ZMod q) ^ (3 * p) = 1 := by
      rw [← hy2, ← pow_mul, show 2 * (3 * p) = q - 1 by dsimp [q]; omega]
      exact ZMod.pow_card_sub_one_eq_one hy0
    rwa [show 3 * p = 2 * p + p by omega, pow_add, h2p, one_mul] at h3p

private theorem proper_bound (p : ℕ) (h : 6 ≤ p) : 6 * p + 2 < 2 ^ p := by
  induction p, h using Nat.le_induction with
  | base => decide
  | succ p hp ih => rw [pow_succ]; omega

/-- Each simultaneous prime value supplies a proper factor, using the cubic criterion. -/
theorem composite_at_pair (hc : H1) (n : ℕ) :
    let p := 2304*n^3 + 2592*n^2 + 972*n + 121
    p.Prime → (6*p+1).Prime → p ∈ OMA.S_oeis_a054723.S := by
  intro p hp hq
  let q := 6*p+1
  have hx : ((24*n+9 : ℕ) : ZMod q) ^ 3 = 2 := by
    have hNat : (24*n+9)^3 = q+2 := (factor_add_two n).symm
    have h := congrArg (fun k : ℕ => (k : ZMod q)) hNat
    rw [Nat.cast_pow, Nat.cast_add q 2, ZMod.natCast_self, zero_add] at h
    exact h
  have hp4 : p % 4 = 1 := by dsimp [p]; omega
  have hd := (hc p hp hp4 hq).2 ⟨_, hx⟩
  have hlarge : 6 ≤ p := by dsimp [p]; omega
  have hlt := proper_bound _ hlarge
  refine ⟨hp, fun hM => ?_⟩
  have heq := (Nat.prime_dvd_prime_iff_eq hq hM).mp hd
  omega

theorem first_example : 357781 ∈ OMA.S_oeis_a054723.S := by
  apply composite_at_pair cubic_criterion 5
  · change Nat.Prime 357781
    norm_num
  · change Nat.Prime 2146687
    norm_num

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a054723.main := by
  intro hc hi
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨n, ⟨hp, hq⟩, hn⟩ := Set.infinite_iff_exists_gt.mp hi B
  exact ⟨_, composite_at_pair hc n hp hq, by omega⟩

end OMA.R_oeis_a054723_R2
