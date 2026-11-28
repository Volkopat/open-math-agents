import OMAStatements.S_oeis_a111184
import Mathlib

namespace OMA.S_oeis_a111184

open Polynomial PowerSeries BigOperators

private abbrev P := Polynomial ℚ
private abbrev PS := PowerSeries P

private lemma ps_coeff_zero_mul {R : Type*} [Semiring R] (f g : PowerSeries R) :
    PowerSeries.coeff 0 (f * g) = PowerSeries.coeff 0 f * PowerSeries.coeff 0 g := by
  simp [PowerSeries.coeff_zero_eq_constantCoeff]

/-- `risingFact a n` evaluated via a ring homomorphism `f`. -/
private lemma map_risingFact {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (a : R) : ∀ n : ℕ, f (risingFact a n) = risingFact (f a) n
  | 0 => by simp [risingFact]
  | n + 1 => by simp [risingFact, map_risingFact f a n]

/-- Rising factorial shift identity: `a * risingFact (a + 1) n = risingFact a (n + 1)`. -/
private lemma mul_risingFact_add_one {R : Type*} [CommSemiring R] (a : R) :
    ∀ n : ℕ, a * risingFact (a + 1) n = risingFact a (n + 1)
  | 0 => by simp [risingFact]
  | n + 1 => by
      simp only [risingFact]
      rw [← mul_assoc, mul_risingFact_add_one a n]
      congr 1
      push_cast
      ring

/-- Rising factorial difference identity:
`risingFact (a + 1) (n + 1) - risingFact a (n + 1) = (n + 1) * risingFact (a + 1) n`. -/
private lemma risingFact_add_one_sub {R : Type*} [CommRing R] (a : R) (n : ℕ) :
    risingFact (a + 1) (n + 1) - risingFact a (n + 1) =
      ((n + 1 : ℕ) : R) * risingFact (a + 1) n := by
  rw [← mul_risingFact_add_one a n]
  simp only [risingFact]
  push_cast
  ring

/-- Rising factorial at `1` is factorial: `risingFact (1 : R) n = (n! : R)`. -/
private lemma risingFact_one {R : Type*} [CommSemiring R] :
    ∀ n : ℕ, risingFact (1 : R) n = (Nat.factorial n : R)
  | 0 => by simp [risingFact]
  | n + 1 => by
      simp only [risingFact, risingFact_one n, Nat.factorial_succ]
      push_cast
      ring

/-- Rising factorial at `2` is `(n + 1)!`. -/
private lemma risingFact_two {R : Type*} [CommSemiring R] (n : ℕ) :
    risingFact (2 : R) n = (Nat.factorial (n + 1) : R) := by
  have h := mul_risingFact_add_one (1 : R) n
  have h1 : (1 : R) + 1 = 2 := by ring
  rw [h1, one_mul, risingFact_one] at h
  exact h

/-- Hypergeometric formal power series `H_{a, b}(t) = ∑_{n ≥ 0} (a)_n * (b)_n / n! * t^n` over `P = ℚ[X]`. -/
private noncomputable def hypSeries (a b : P) : PS :=
  PowerSeries.mk fun n =>
    Polynomial.C ((Nat.factorial n : ℚ)⁻¹) * risingFact a n * risingFact b n

private lemma coeff_hypSeries (a b : P) (n : ℕ) :
    PowerSeries.coeff n (hypSeries a b) =
      Polynomial.C ((Nat.factorial n : ℚ)⁻¹) * risingFact a n * risingFact b n :=
  PowerSeries.coeff_mk n _

private lemma hypSeries_comm (a b : P) : hypSeries a b = hypSeries b a := by
  apply PowerSeries.ext; intro n
  simp only [coeff_hypSeries]; ring

private lemma coeff_zero_hypSeries (a b : P) : PowerSeries.coeff 0 (hypSeries a b) = 1 := by
  simp [coeff_hypSeries, risingFact]

/-- Contiguous relation 1: `H_{a, b+1} - H_{a, b} = a * t * H_{a+1, b+1}`. -/
private lemma hypSeries_sub_right (a b : P) :
    hypSeries a (b + 1) - hypSeries a b =
      PowerSeries.C a * PowerSeries.X * hypSeries (a + 1) (b + 1) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [map_sub, coeff_zero_hypSeries, coeff_zero_hypSeries, sub_self,
          mul_assoc (PowerSeries.C a), PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul, mul_zero]
  | succ n =>
      rw [map_sub, coeff_hypSeries, coeff_hypSeries, mul_assoc (PowerSeries.C a),
          PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, coeff_hypSeries]
      have hfac : ((Nat.factorial (n + 1) : ℚ)⁻¹) =
          ((Nat.factorial n : ℚ)⁻¹) * (((n + 1 : ℕ) : ℚ)⁻¹) := by
        rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, mul_comm]
      have hpos : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hsub := risingFact_add_one_sub b n
      have hmul := mul_risingFact_add_one a n
      calc
        Polynomial.C ((Nat.factorial (n + 1) : ℚ)⁻¹) * risingFact a (n + 1) * risingFact (b + 1) (n + 1) -
            Polynomial.C ((Nat.factorial (n + 1) : ℚ)⁻¹) * risingFact a (n + 1) * risingFact b (n + 1)
          = Polynomial.C ((Nat.factorial (n + 1) : ℚ)⁻¹) * risingFact a (n + 1) *
              (risingFact (b + 1) (n + 1) - risingFact b (n + 1)) := by ring
        _ = Polynomial.C ((Nat.factorial (n + 1) : ℚ)⁻¹) * risingFact a (n + 1) *
              (((n + 1 : ℕ) : P) * risingFact (b + 1) n) := by rw [hsub]
        _ = Polynomial.C ((Nat.factorial n : ℚ)⁻¹) *
              Polynomial.C (((n + 1 : ℕ) : ℚ)⁻¹ * ((n + 1 : ℕ) : ℚ)) *
              (a * risingFact (a + 1) n) * risingFact (b + 1) n := by
              rw [hfac, ← hmul, map_mul, map_mul]
              simp only [Polynomial.C_eq_natCast]
              ring
        _ = a * (Polynomial.C ((Nat.factorial n : ℚ)⁻¹) * risingFact (a + 1) n * risingFact (b + 1) n) := by
              rw [inv_mul_cancel₀ hpos, map_one, mul_one]; ring

/-- Contiguous relation 2: `H_{a+1, b} - H_{a, b} = b * t * H_{a+1, b+1}`. -/
private lemma hypSeries_sub_left (a b : P) :
    hypSeries (a + 1) b - hypSeries a b =
      PowerSeries.C b * PowerSeries.X * hypSeries (a + 1) (b + 1) := by
  rw [hypSeries_comm (a + 1) b, hypSeries_comm a b, hypSeries_comm (a + 1) (b + 1)]
  exact hypSeries_sub_right b a

/-- Alternating hypergeometric sequence `A_k(t)`:
`A_{2j} = H_{X + j, j + 1}`, `A_{2j+1} = H_{X + j, j + 2}`. -/
private noncomputable def altA (k : ℕ) : PS :=
  if k % 2 = 0 then
    hypSeries (Polynomial.X + Polynomial.C ((k / 2 : ℕ) : ℚ)) (Polynomial.C ((k / 2 + 1 : ℕ) : ℚ))
  else
    hypSeries (Polynomial.X + Polynomial.C ((k / 2 : ℕ) : ℚ)) (Polynomial.C ((k / 2 + 2 : ℕ) : ℚ))

private lemma coeff_zero_altA (k : ℕ) : PowerSeries.coeff 0 (altA k) = 1 := by
  unfold altA; split_ifs <;> exact coeff_zero_hypSeries _ _

/-- Uniform recurrence for `altA`: `altA (k + 1) - altA k = deltaC k * X * altA (k + 2)`. -/
private lemma altA_recurrence (k : ℕ) :
    altA (k + 1) - altA k = PowerSeries.C (deltaC k) * PowerSeries.X * altA (k + 2) := by
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h0 : (j + j) % 2 = 0 := by omega
    have h1 : (j + j + 1) % 2 = 1 := by omega
    have h2 : (j + j + 2) % 2 = 0 := by omega
    have hd0 : (j + j) / 2 = j := by omega
    have hd1 : (j + j + 1) / 2 = j := by omega
    have hd2 : (j + j + 2) / 2 = j + 1 := by omega
    simp only [altA, deltaC, h0, h1, h2, hd0, hd1, hd2, ↓reduceIte, Nat.one_ne_zero]
    have ha : Polynomial.X + Polynomial.C ((j + 1 : ℕ) : ℚ) =
        (Polynomial.X + Polynomial.C (j : ℚ)) + 1 := by
      push_cast; simp only [map_add, map_one]; ring
    have hb : Polynomial.C ((j + 2 : ℕ) : ℚ) = Polynomial.C ((j + 1 : ℕ) : ℚ) + 1 := by
      push_cast; simp only [map_add, map_one, map_ofNat]; ring
    have hc : Polynomial.C (j : ℚ) + Polynomial.X = Polynomial.X + Polynomial.C (j : ℚ) := by ring
    rw [ha, hb, hc]
    exact hypSeries_sub_right (Polynomial.X + Polynomial.C (j : ℚ)) (Polynomial.C ((j + 1 : ℕ) : ℚ))
  · have h0 : (2 * j + 1) % 2 = 1 := by omega
    have h1 : (2 * j + 1 + 1) % 2 = 0 := by omega
    have h2 : (2 * j + 1 + 2) % 2 = 1 := by omega
    have hd0 : (2 * j + 1) / 2 = j := by omega
    have hd1 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    have hd2 : (2 * j + 1 + 2) / 2 = j + 1 := by omega
    simp only [altA, deltaC, h0, h1, h2, hd0, hd1, hd2, ↓reduceIte, Nat.one_ne_zero]
    have ha : Polynomial.X + Polynomial.C ((j + 1 : ℕ) : ℚ) =
        (Polynomial.X + Polynomial.C (j : ℚ)) + 1 := by
      push_cast; simp only [map_add, map_one]; ring
    have hb : Polynomial.C ((j + 1 + 2 : ℕ) : ℚ) = Polynomial.C ((j + 2 : ℕ) : ℚ) + 1 := by
      push_cast; simp only [map_add, map_one, map_ofNat]; ring
    have hb1 : Polynomial.C ((j + 1 + 1 : ℕ) : ℚ) = Polynomial.C ((j + 2 : ℕ) : ℚ) := by
      push_cast; simp only [map_add, map_one, map_ofNat]; ring
    rw [ha, hb, hb1]
    exact hypSeries_sub_left (Polynomial.X + Polynomial.C (j : ℚ)) (Polynomial.C ((j + 2 : ℕ) : ℚ))

/-- `W_0(t) = altA 0 = ∑_{n ≥ 0} (X)_n t^n`. -/
private noncomputable def W0 : PS :=
  PowerSeries.mk fun n => risingFact Polynomial.X n

private lemma altA_zero_eq_W0 : altA 0 = W0 := by
  apply PowerSeries.ext; intro n
  simp only [altA, Nat.zero_mod, ↓reduceIte, coeff_hypSeries, W0, PowerSeries.coeff_mk]
  have h1 : Polynomial.X + Polynomial.C ((0 / 2 : ℕ) : ℚ) = Polynomial.X := by simp
  have h2 : Polynomial.C ((0 / 2 + 1 : ℕ) : ℚ) = (1 : P) := by simp
  rw [h1, h2, risingFact_one]
  have hpos : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  calc
    Polynomial.C ((Nat.factorial n : ℚ)⁻¹) * risingFact Polynomial.X n * (Nat.factorial n : P)
      = Polynomial.C ((Nat.factorial n : ℚ)⁻¹ * (Nat.factorial n : ℚ)) * risingFact Polynomial.X n := by
          rw [map_mul]; simp only [Polynomial.C_eq_natCast]; ring
    _ = risingFact Polynomial.X n := by rw [inv_mul_cancel₀ hpos, map_one, one_mul]

private lemma altA_one_coeff (n : ℕ) :
    PowerSeries.coeff n (altA 1) = ((n + 1 : ℕ) : P) * risingFact Polynomial.X n := by
  have h1mod : 1 % 2 ≠ 0 := by decide
  simp only [altA, h1mod, ↓reduceIte, coeff_hypSeries]
  have h1 : Polynomial.X + Polynomial.C ((1 / 2 : ℕ) : ℚ) = Polynomial.X := by simp
  have h2 : Polynomial.C ((1 / 2 + 2 : ℕ) : ℚ) = (2 : P) := by
    have : ((1 / 2 + 2 : ℕ) : ℚ) = (2 : ℚ) := by norm_num
    rw [this, map_ofNat]
  rw [h1, h2, risingFact_two, Nat.factorial_succ]
  have hpos : (Nat.factorial n : ℚ) ≠ 0 := by positivity
  calc
    Polynomial.C ((Nat.factorial n : ℚ)⁻¹) * risingFact Polynomial.X n * (((n + 1) * Nat.factorial n : ℕ) : P)
      = Polynomial.C ((Nat.factorial n : ℚ)⁻¹ * (Nat.factorial n : ℚ)) *
          ((n + 1 : ℕ) : P) * risingFact Polynomial.X n := by
          rw [map_mul]; push_cast; simp only [Polynomial.C_eq_natCast]; ring
    _ = ((n + 1 : ℕ) : P) * risingFact Polynomial.X n := by
          rw [inv_mul_cancel₀ hpos, map_one, one_mul]

/-- `W0` is a unit in `PS = PowerSeries (Polynomial ℚ)` since its constant term is `1`. -/
private lemma isUnit_W0 : IsUnit W0 := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have : PowerSeries.constantCoeff W0 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, W0, PowerSeries.coeff_mk, risingFact]
  rw [this]
  exact isUnit_one

/-- `invW0 * W0 = 1`. -/
private noncomputable def invW0 : PS :=
  ((isUnit_W0.unit⁻¹ : PSˣ) : PS)

private lemma invW0_mul_W0 : invW0 * W0 = 1 := by
  simp [invW0]

private lemma W0_mul_invW0 : W0 * invW0 = 1 := by
  simp [invW0]

private lemma coeff_zero_invW0 : PowerSeries.coeff 0 invW0 = 1 := by
  have h := congr_arg (PowerSeries.coeff 0) invW0_mul_W0
  rw [ps_coeff_zero_mul, PowerSeries.coeff_one] at h
  have hw0 : PowerSeries.coeff 0 W0 = 1 := by simp [W0, risingFact]
  simpa [hw0] using h

/-- `ratioW k = altA (k + 1) * invW0`. -/
private noncomputable def ratioW (k : ℕ) : PS :=
  altA (k + 1) * invW0

private lemma coeff_zero_ratioW (k : ℕ) : PowerSeries.coeff 0 (ratioW k) = 1 := by
  rw [ratioW, ps_coeff_zero_mul, coeff_zero_altA, coeff_zero_invW0, mul_one]

private lemma ratioW_zero_eq :
    ratioW 0 = 1 + PowerSeries.C (deltaC 0) * PowerSeries.X * ratioW 1 := by
  have h := congr_arg (· * invW0) (altA_recurrence 0)
  simp only [sub_mul] at h
  rw [altA_zero_eq_W0, W0_mul_invW0] at h
  have h' : ratioW 0 - 1 = PowerSeries.C (deltaC 0) * PowerSeries.X * ratioW 1 := by
    simpa [ratioW, mul_assoc] using h
  exact eq_add_of_sub_eq' (by rw [sub_eq_add_neg]; simpa [sub_eq_add_neg, add_comm] using h')

private lemma ratioW_succ_eq (k : ℕ) :
    ratioW (k + 1) = ratioW k + PowerSeries.C (deltaC (k + 1)) * PowerSeries.X * ratioW (k + 2) := by
  have h := congr_arg (· * invW0) (altA_recurrence (k + 1))
  simp only [sub_mul] at h
  have h' : ratioW (k + 1) - ratioW k =
      PowerSeries.C (deltaC (k + 1)) * PowerSeries.X * ratioW (k + 2) := by
    simpa [ratioW, mul_assoc] using h
  rw [← h']; ring

/-- `deltaDyck k k = 1` for all `k`. -/
private lemma deltaDyck_diag : ∀ k : ℕ, deltaDyck k k = 1
  | 0 => rfl
  | k + 1 => by
      have hvan : ∀ m j : ℕ, m < j → deltaDyck m j = 0 := by
        intro m
        induction m with
        | zero =>
            intro j hj
            cases j with
            | zero => omega
            | succ j => rfl
        | succ m ih =>
            intro j hj
            simp only [deltaDyck]
            have h1 : (if j = 0 then 0 else deltaDyck m (j - 1)) = 0 := by
              split_ifs with h
              · rfl
              · exact ih (j - 1) (by omega)
            have h2 : deltaDyck m (j + 1) = 0 := ih (j + 1) (by omega)
            rw [h1, h2, mul_zero, add_zero]
      simp only [deltaDyck, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [hvan k (k + 2) (by omega), mul_zero, add_zero, deltaDyck_diag k]

/-- Key Bridge Theorem 1: `deltaDyck (2 * n + k) k = coeff n (ratioW k)` for all `n, k`. -/
private lemma deltaDyck_eq_coeff_ratioW :
    ∀ n k : ℕ, deltaDyck (2 * n + k) k = PowerSeries.coeff n (ratioW k)
  | 0, k => by
      simp only [Nat.mul_zero, zero_add, deltaDyck_diag, coeff_zero_ratioW]
  | n + 1, 0 => by
      have hlhs : deltaDyck (2 * (n + 1) + 0) 0 = deltaC 0 * deltaDyck (2 * n + 1) 1 := by
        have : 2 * (n + 1) + 0 = (2 * n + 1) + 1 := by omega
        rw [this, deltaDyck]
        simp
      have hrhs : PowerSeries.coeff (n + 1) (ratioW 0) =
          deltaC 0 * PowerSeries.coeff n (ratioW 1) := by
        rw [ratioW_zero_eq, map_add, PowerSeries.coeff_one]
        simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add, mul_assoc,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
      rw [hlhs, hrhs, deltaDyck_eq_coeff_ratioW n 1]
  | n + 1, k + 1 => by
      have hlhs : deltaDyck (2 * (n + 1) + (k + 1)) (k + 1) =
          deltaDyck (2 * (n + 1) + k) k + deltaC (k + 1) * deltaDyck (2 * n + (k + 2)) (k + 2) := by
        have h1 : 2 * (n + 1) + (k + 1) = (2 * (n + 1) + k) + 1 := by omega
        have h2 : 2 * (n + 1) + k = 2 * n + (k + 2) := by omega
        rw [h1, deltaDyck]
        simp [h2]
      have hrhs : PowerSeries.coeff (n + 1) (ratioW (k + 1)) =
          PowerSeries.coeff (n + 1) (ratioW k) +
            deltaC (k + 1) * PowerSeries.coeff n (ratioW (k + 2)) := by
        rw [ratioW_succ_eq k, map_add, mul_assoc, PowerSeries.coeff_C_mul,
            PowerSeries.coeff_succ_X_mul]
      rw [hlhs, hrhs, deltaDyck_eq_coeff_ratioW (n + 1) k, deltaDyck_eq_coeff_ratioW n (k + 2)]

/-- Corollary: `a111184Poly n = coeff n (ratioW 0) = coeff n (altA 1 * invW0)`. -/
private lemma a111184Poly_eq_coeff_ratioW (n : ℕ) :
    a111184Poly n = PowerSeries.coeff n (ratioW 0) := by
  simpa [a111184Poly] using deltaDyck_eq_coeff_ratioW n 0

/-- `Z_d(t) = ∑_{n ≥ 0} (n + 1) * (X + d + 1)_n * t^n` for Kurkov's Conjecture 3. -/
private noncomputable def seriesZ (d : ℕ) : PS :=
  PowerSeries.mk fun n =>
    ((n + 1 : ℕ) : P) * risingFact (Polynomial.X + Polynomial.C ((d + 1 : ℕ) : ℚ)) n

private lemma coeff_seriesZ (d n : ℕ) :
    PowerSeries.coeff n (seriesZ d) =
      ((n + 1 : ℕ) : P) * risingFact (Polynomial.X + Polynomial.C ((d + 1 : ℕ) : ℚ)) n :=
  PowerSeries.coeff_mk n _

/-- `altA 1 = W0 + X * t * Z_0`. -/
private lemma altA_one_eq_W0_add :
    altA 1 = W0 + PowerSeries.C Polynomial.X * PowerSeries.X * seriesZ 0 := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [altA_one_coeff, map_add, W0, PowerSeries.coeff_mk, mul_assoc (PowerSeries.C Polynomial.X),
          PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul, mul_zero, add_zero]
      simp [risingFact]
  | succ n =>
      rw [altA_one_coeff, map_add, W0, PowerSeries.coeff_mk, mul_assoc (PowerSeries.C Polynomial.X),
          PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, coeff_seriesZ]
      have h1 : Polynomial.X + Polynomial.C ((0 + 1 : ℕ) : ℚ) = Polynomial.X + 1 := by simp
      rw [h1, mul_left_comm Polynomial.X, mul_risingFact_add_one Polynomial.X n]
      push_cast
      ring

/-- `S_d(t) = Z_d(t) * invW0`. -/
private noncomputable def seriesS (d : ℕ) : PS :=
  seriesZ d * invW0

private lemma coeff_zero_seriesS (d : ℕ) : PowerSeries.coeff 0 (seriesS d) = 1 := by
  rw [seriesS, ps_coeff_zero_mul, coeff_seriesZ, coeff_zero_invW0]
  simp [risingFact]

/-- `ratioW 0 = 1 + X * t * seriesS 0`. -/
private lemma ratioW_zero_eq_one_add_seriesS :
    ratioW 0 = 1 + PowerSeries.C Polynomial.X * PowerSeries.X * seriesS 0 := by
  have h := congr_arg (· * invW0) altA_one_eq_W0_add
  simp only [add_mul, W0_mul_invW0] at h
  simpa [ratioW, seriesS, mul_assoc] using h

/-- For `n ≥ 1`, `a111184Poly n = X * coeff (n - 1) (seriesS 0)`. -/
private lemma a111184Poly_eq_X_mul_seriesS {n : ℕ} (hn : 0 < n) :
    a111184Poly n = Polynomial.X * PowerSeries.coeff (n - 1) (seriesS 0) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  rw [a111184Poly_eq_coeff_ratioW, ratioW_zero_eq_one_add_seriesS, map_add, PowerSeries.coeff_one]
  simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add, mul_assoc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, Nat.succ_sub_one]

/-- Key Z-recurrence at `d = 0`: `Z_0 - W_0 = t * ((X + 1) * Z_1 + Z_0)`. -/
private lemma seriesZ_zero_rec :
    seriesZ 0 - W0 =
      PowerSeries.X * (PowerSeries.C (Polynomial.X + 1) * seriesZ 1 + seriesZ 0) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [map_sub, coeff_seriesZ, W0, PowerSeries.coeff_mk, PowerSeries.coeff_zero_X_mul]
      simp [risingFact]
  | succ n =>
      rw [map_sub, coeff_seriesZ, W0, PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul,
          map_add, PowerSeries.coeff_C_mul, coeff_seriesZ, coeff_seriesZ]
      have h0 : Polynomial.X + Polynomial.C ((0 + 1 : ℕ) : ℚ) = Polynomial.X + 1 := by simp
      have h1 : Polynomial.X + Polynomial.C ((1 + 1 : ℕ) : ℚ) = (Polynomial.X + 1) + 1 := by
        have : ((1 + 1 : ℕ) : ℚ) = 2 := by norm_num
        rw [this, map_ofNat]; ring
      rw [h0, h1, mul_left_comm (Polynomial.X + 1), mul_risingFact_add_one (Polynomial.X + 1) n,
          ← mul_risingFact_add_one Polynomial.X n]
      simp only [risingFact]
      push_cast
      ring

/-- Key Z-recurrence at `d + 1`:
`Z_{d+1} - Z_d = t * ((X + d + 2) * Z_{d+2} - (X + d) * Z_{d+1})`. -/
private lemma seriesZ_succ_rec (d : ℕ) :
    seriesZ (d + 1) - seriesZ d =
      PowerSeries.X *
        (PowerSeries.C (Polynomial.X + Polynomial.C ((d + 2 : ℕ) : ℚ)) * seriesZ (d + 2) -
         PowerSeries.C (Polynomial.X + Polynomial.C (d : ℚ)) * seriesZ (d + 1)) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [map_sub, coeff_seriesZ, coeff_seriesZ, PowerSeries.coeff_zero_X_mul]
      simp [risingFact]
  | succ n =>
      rw [map_sub, coeff_seriesZ, coeff_seriesZ, PowerSeries.coeff_succ_X_mul,
          map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, coeff_seriesZ, coeff_seriesZ]
      set a : P := Polynomial.X + Polynomial.C ((d + 1 : ℕ) : ℚ)
      have ha1 : Polynomial.X + Polynomial.C ((d + 1 + 1 : ℕ) : ℚ) = a + 1 := by
        simp only [a]; push_cast; simp only [map_add, map_one]; ring
      have ha2 : Polynomial.X + Polynomial.C ((d + 2 + 1 : ℕ) : ℚ) = (a + 1) + 1 := by
        simp only [a]; push_cast; simp only [map_add, map_one, map_ofNat]; ring
      have hc0 : Polynomial.X + Polynomial.C (d : ℚ) = a - 1 := by
        simp only [a]; push_cast; simp only [map_add, map_one]; ring
      rw [ha1, ha2, hc0, ← mul_sub, risingFact_add_one_sub a n, mul_left_comm (a + 1),
          mul_risingFact_add_one (a + 1) n]
      simp only [risingFact]
      push_cast
      ring

/-- Coefficient recurrence for `seriesS 0`:
`coeff (i + 1) (seriesS 0) = (X + 1) * coeff i (seriesS 1) + coeff i (seriesS 0)`. -/
private lemma coeff_seriesS_zero_succ (i : ℕ) :
    PowerSeries.coeff (i + 1) (seriesS 0) =
      (Polynomial.X + 1) * PowerSeries.coeff i (seriesS 1) + PowerSeries.coeff i (seriesS 0) := by
  have h := congr_arg (· * invW0) seriesZ_zero_rec
  simp only [sub_mul, W0_mul_invW0, mul_assoc, add_mul] at h
  have h' : seriesS 0 - 1 =
      PowerSeries.X * (PowerSeries.C (Polynomial.X + 1) * seriesS 1 + seriesS 0) := by
    simpa [seriesS, mul_assoc, mul_add] using h
  have hc := congr_arg (PowerSeries.coeff (i + 1)) h'
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_succ_X_mul,
      map_add, PowerSeries.coeff_C_mul] at hc
  simpa using hc

/-- Coefficient difference recurrence for `seriesS (d + 1)`:
`coeff (i + 1) (seriesS (d + 1)) - coeff (i + 1) (seriesS d) =
  (X + d + 2) * coeff i (seriesS (d + 2)) - (X + d) * coeff i (seriesS (d + 1))`. -/
private lemma coeff_seriesS_succ_sub (i d : ℕ) :
    PowerSeries.coeff (i + 1) (seriesS (d + 1)) - PowerSeries.coeff (i + 1) (seriesS d) =
      (Polynomial.X + Polynomial.C ((d + 2 : ℕ) : ℚ)) * PowerSeries.coeff i (seriesS (d + 2)) -
      (Polynomial.X + Polynomial.C (d : ℚ)) * PowerSeries.coeff i (seriesS (d + 1)) := by
  have h := congr_arg (· * invW0) (seriesZ_succ_rec d)
  simp only [sub_mul, mul_assoc] at h
  have h' : seriesS (d + 1) - seriesS d =
      PowerSeries.X *
        (PowerSeries.C (Polynomial.X + Polynomial.C ((d + 2 : ℕ) : ℚ)) * seriesS (d + 2) -
         PowerSeries.C (Polynomial.X + Polynomial.C (d : ℚ)) * seriesS (d + 1)) := by
    simpa [seriesS, mul_assoc, mul_sub] using h
  have hc := congr_arg (PowerSeries.coeff (i + 1)) h'
  rw [map_sub, PowerSeries.coeff_succ_X_mul, map_sub,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at hc
  exact hc

/-- Cumulative sum form matching Kurkov's Conjecture 3 inner loop:
`coeff (i + 1) (seriesS d) = (X + d) * coeff i (seriesS (d + 1)) + ∑_{r=0}^{d+1} coeff i (seriesS r)`. -/
private lemma coeff_seriesS_sum_rec (i : ℕ) :
    ∀ d : ℕ,
      PowerSeries.coeff (i + 1) (seriesS d) =
        (Polynomial.X + Polynomial.C (d : ℚ)) * PowerSeries.coeff i (seriesS (d + 1)) +
          ∑ r ∈ Finset.range (d + 2), PowerSeries.coeff i (seriesS r)
  | 0 => by
      rw [coeff_seriesS_zero_succ, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [Nat.cast_zero, map_zero, add_zero]
      ring
  | d + 1 => by
      have hsub := coeff_seriesS_succ_sub i d
      have hprev := coeff_seriesS_sum_rec i d
      rw [Finset.sum_range_succ]
      have hadd : PowerSeries.coeff (i + 1) (seriesS (d + 1)) =
          PowerSeries.coeff (i + 1) (seriesS d) +
            ((Polynomial.X + Polynomial.C ((d + 2 : ℕ) : ℚ)) * PowerSeries.coeff i (seriesS (d + 2)) -
             (Polynomial.X + Polynomial.C (d : ℚ)) * PowerSeries.coeff i (seriesS (d + 1))) := by
        rw [← hsub]; ring
      rw [hadd, hprev]
      push_cast
      simp only [map_add, map_one, map_ofNat]
      ring

/-- Invariant of `kurkovInner`: starting from a vector `v` matching `seriesS` at step `i`,
running `kurkovInner m i rem A v` produces `seriesS` at step `i + 1` on `j ∈ [m - rem, m)`
and leaves indices `< m - rem` untouched. -/
private lemma kurkovInner_spec (m i : ℕ) :
    ∀ (rem : ℕ) (_hrem : rem ≤ m - (i + 1)) (A : P) (v : ℕ → P),
      (∀ k, m - rem ≤ k → k < m → v k = PowerSeries.coeff i (seriesS (k - i))) →
      A = ∑ r ∈ Finset.range (m - rem - i), PowerSeries.coeff i (seriesS r) →
      (∀ k, k < m - rem → kurkovInner m i rem A v k = v k) ∧
      (∀ k, m - rem ≤ k → k < m →
        kurkovInner m i rem A v k = PowerSeries.coeff (i + 1) (seriesS (k - (i + 1))))
  | 0, _, _, v, _, _ => by
      simp only [kurkovInner, Nat.sub_zero]
      exact ⟨fun _ _ => trivial, fun k hk1 hk2 => by omega⟩
  | rem + 1, _hrem, A, v, hv, hA => by
      simp only [kurkovInner]
      set j := m - (rem + 1)
      set A' := A + v j
      set vj' := (Polynomial.C (((j - i : ℕ) : ℚ) - 1) + Polynomial.X) * v j + A'
      have hj_gt : i < j := by omega
      have hj_lt : j < m := by omega
      have hmj : m - rem = j + 1 := by omega
      have hA' : A' = ∑ r ∈ Finset.range (m - rem - i), PowerSeries.coeff i (seriesS r) := by
        have hlen : m - rem - i = (j - i) + 1 := by omega
        rw [hlen, Finset.sum_range_succ, ← hA]
        have hvj : v j = PowerSeries.coeff i (seriesS (j - i)) := hv j (le_refl j) hj_lt
        rw [← hvj]
      have hv' : ∀ k, m - rem ≤ k → k < m →
          Function.update v j vj' k = PowerSeries.coeff i (seriesS (k - i)) := by
        intro k hk1 hk2
        have hne : k ≠ j := by omega
        rw [Function.update_of_ne hne]
        exact hv k (by omega) hk2
      have ih := kurkovInner_spec m i rem (by omega) A' (Function.update v j vj') hv' hA'
      refine ⟨?_, ?_⟩
      · intro k hk
        have hne : k ≠ j := by omega
        rw [ih.1 k (by omega), Function.update_of_ne hne]
      · intro k hk1 hk2
        by_cases hkj : k = j
        · subst hkj
          rw [ih.1 j (by omega), Function.update_self]
          set d := j - (i + 1)
          have hji : j - i = d + 1 := by omega
          have hlen2 : m - rem - i = d + 2 := by omega
          have hvj : v j = PowerSeries.coeff i (seriesS (d + 1)) := by
            rw [← hji]; exact hv j (le_refl j) hj_lt
          rw [coeff_seriesS_sum_rec i d]
          simp only [vj']
          rw [hA', hlen2, hvj, hji]
          push_cast
          simp only [map_sub, map_add, map_one]
          ring
        · exact ih.2 k (by omega) hk2

/-- Invariant of `kurkovOuter`: after `t` outer steps (from `i = 0` to `t - 1`),
for `k < t`, `v k = coeff k (seriesS 0)`, and for `t ≤ k < m`, `v k = coeff t (seriesS (k - t))`. -/
private lemma kurkovOuter_spec (m : ℕ) (hm : 1 < m) :
    ∀ (steps : ℕ) (_hsteps : steps ≤ m - 1) (v : ℕ → P),
      let t := (m - 1) - steps
      (∀ k, k < t → v k = PowerSeries.coeff k (seriesS 0)) →
      (∀ k, t ≤ k → k < m → v k = PowerSeries.coeff t (seriesS (k - t))) →
      ∀ k, k < m → kurkovOuter m steps v k = PowerSeries.coeff k (seriesS 0)
  | 0, _, v, hv1, hv2, k, hk => by
      simp only [kurkovOuter]
      by_cases hkt : k < m - 1
      · exact hv1 k (by omega)
      · have hkeq : k = m - 1 := by omega
        subst hkeq
        simpa using hv2 (m - 1) (by omega) hk
  | steps + 1, _hsteps, v, hv1, hv2, k, hk => by
      simp only [kurkovOuter]
      set t := (m - 1) - (steps + 1)
      have ht_lt : t < m - 1 := by omega
      have hrem_eq : m - (m - (t + 1)) = t + 1 := by omega
      have hA : v t = ∑ r ∈ Finset.range (m - (m - (t + 1)) - t), PowerSeries.coeff t (seriesS r) := by
        rw [hrem_eq, Nat.add_sub_cancel_left, Finset.sum_range_one]
        simpa using hv2 t (le_refl t) (by omega)
      have hv_inner : ∀ k', m - (m - (t + 1)) ≤ k' → k' < m →
          v k' = PowerSeries.coeff t (seriesS (k' - t)) := by
        intro k' hk1 hk2
        exact hv2 k' (by omega) hk2
      have hspec := kurkovInner_spec m t (m - (t + 1)) (le_refl _) (v t) v hv_inner hA
      have ht_next : (m - 1) - steps = t + 1 := by omega
      apply kurkovOuter_spec m hm steps (by omega) (kurkovInner m t (m - (t + 1)) (v t) v)
      · intro k' hk'
        rw [ht_next] at hk'
        by_cases hlt : k' < t
        · rw [hspec.1 k' (by omega)]
          exact hv1 k' hlt
        · have heq : k' = t := by omega
          subst heq
          rw [hspec.1 t (by omega)]
          simpa using hv2 t (le_refl t) (by omega)
      · intro k' hk1 hk2
        rw [ht_next] at hk1 ⊢
        exact hspec.2 k' (by omega) hk2
      · exact hk

/-- Proof of Conjecture 3: `a111184Poly n = X * kurkovVec m (n - 1)` for `0 < n ≤ m`. -/
private lemma conj3_proof (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    a111184Poly n = Polynomial.X * kurkovVec m (n - 1) := by
  rw [a111184Poly_eq_X_mul_seriesS hn]
  congr 1
  unfold kurkovVec
  by_cases hm1 : m ≤ 1
  · have hn1 : n = 1 := by omega
    subst hn1
    simp [hm1, coeff_zero_seriesS]
  · simp only [hm1, ↓reduceIte]
    have hm : 1 < m := by omega
    have h := kurkovOuter_spec m hm (m - 1) (le_refl _) (fun _ => 1)
      (fun k hk => by omega)
      (fun k _ _ => by simp [coeff_zero_seriesS])
      (n - 1) (by omega)
    exact h.symm

/-- Evaluation of `a111184Poly n` at `q : ℚ` as `∑_{k=1}^n T(n, k) q^k`. -/
private lemma a111184Poly_eval (n : ℕ) (hn : 0 < n) (q : ℚ) :
    (a111184Poly n).eval q = q * ∑ k ∈ Finset.Icc 1 n, a111184 n k * q ^ (k - 1) := by
  have hdeg : (a111184Poly n).natDegree ≤ n := by
    have hvan_lt : ∀ m' j', m' < j' → deltaDyck m' j' = 0 := by
      intro m'
      induction m' with
      | zero =>
          intro j' hj'
          cases j' with
          | zero => omega
          | succ j' => rfl
      | succ m' ihm' =>
          intro j' hj'
          simp only [deltaDyck]
          have h1 : (if j' = 0 then 0 else deltaDyck m' (j' - 1)) = 0 := by
            split_ifs with hz
            · rfl
            · exact ihm' (j' - 1) (by omega)
          have h2 : deltaDyck m' (j' + 1) = 0 := ihm' (j' + 1) (by omega)
          rw [h1, h2, mul_zero, add_zero]
    have hdeg_dyck : ∀ m k, (deltaDyck m k).natDegree ≤ (m - k) / 2 := by
      intro m
      induction m with
      | zero =>
          intro k
          cases k <;> simp [deltaDyck]
      | succ m ih =>
          intro k
          simp only [deltaDyck]
          refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
          · split_ifs with hk
            · simp
            · exact le_trans (ih (k - 1)) (by omega)
          · by_cases hlt : m < k + 1
            · rw [hvan_lt m (k + 1) hlt, mul_zero]; simp
            · refine le_trans (Polynomial.natDegree_mul_le) ?_
              have hdc : (deltaC k).natDegree ≤ if k % 2 = 0 then 1 else 0 := by
                unfold deltaC
                split_ifs
                · exact le_trans (Polynomial.natDegree_add_le _ _) (by simp)
                · simp
              have hih := ih (k + 1)
              by_cases hk : k % 2 = 0
              · simp only [hk, ↓reduceIte] at hdc
                omega
              · simp only [hk, ↓reduceIte] at hdc
                omega
    simpa [a111184Poly] using hdeg_dyck (2 * n) 0
  have hzero : (a111184Poly n).coeff 0 = 0 := by
    rw [a111184Poly_eq_X_mul_seriesS hn, Polynomial.coeff_X_mul_zero]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
  rw [Finset.sum_range_succ', hzero, pow_zero, mul_one, add_zero, Finset.mul_sum]
  rw [show Finset.Icc 1 n = (Finset.range n).image (· + 1) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨a, ha, rfl⟩; omega]
  rw [Finset.sum_image (by intro a _ b _ hab; dsimp at hab; omega)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [a111184, Nat.add_sub_cancel]
  ring

/-- `W0` satisfies `X * t * Z_0 = t * W0'`, i.e., `altA 1 = W0 + t * W0'`. -/
private lemma altA_one_eq_W0_add_X_mul_deriv :
    altA 1 = W0 + PowerSeries.X * PowerSeries.derivative P W0 := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      simp [altA_one_coeff, W0, risingFact]
  | succ n =>
      rw [altA_one_coeff, map_add, W0, PowerSeries.coeff_mk, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
      push_cast
      ring

/-- Evaluation ring homomorphism `PowerSeries (Polynomial ℚ) →+* PowerSeries ℚ` at `X = q`. -/
private noncomputable def evalPS (q : ℚ) : PS →+* PowerSeries ℚ :=
  PowerSeries.map (Polynomial.evalRingHom q)

private lemma evalPS_W0 (q : ℚ) : evalPS q W0 = risingSeries q := by
  apply PowerSeries.ext; intro n
  simp only [evalPS, PowerSeries.coeff_map, W0, risingSeries, PowerSeries.coeff_mk,
    Polynomial.coe_evalRingHom]
  have h := map_risingFact (Polynomial.evalRingHom q) Polynomial.X n
  simpa using h

private lemma evalPS_derivative (q : ℚ) (f : PS) :
    evalPS q (PowerSeries.derivative P f) = PowerSeries.derivative ℚ (evalPS q f) := by
  apply PowerSeries.ext; intro n
  simp [evalPS, PowerSeries.coeff_map, PowerSeries.coeff_derivative]

private lemma evalPS_invW0 (q : ℚ) : evalPS q invW0 = (risingSeries q)⁻¹ := by
  have hmul : evalPS q invW0 * risingSeries q = 1 := by
    rw [← evalPS_W0 q, ← map_mul, invW0_mul_W0, map_one]
  have hunit : IsUnit (risingSeries q) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have : PowerSeries.constantCoeff (risingSeries q) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, risingSeries, PowerSeries.coeff_mk, risingFact]
    rw [this]; exact isUnit_one
  calc
    evalPS q invW0 = evalPS q invW0 * (risingSeries q * (risingSeries q)⁻¹) := by
      have hc0 : PowerSeries.constantCoeff (risingSeries q) ≠ 0 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff, risingSeries, PowerSeries.coeff_mk, risingFact]
        exact one_ne_zero
      rw [PowerSeries.mul_inv_cancel _ hc0, mul_one]
    _ = (evalPS q invW0 * risingSeries q) * (risingSeries q)⁻¹ := by ring
    _ = (risingSeries q)⁻¹ := by rw [hmul, one_mul]

/-- Proof of Conjecture 1: `∑_{k=1}^n T(n, k) q^(k-1) = a111528 q n` for `n > 0`, `q : ℕ`. -/
private lemma conj1_proof (n : ℕ) (hn : 0 < n) (q : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, a111184 n k * (q : ℚ) ^ (k - 1) = a111528 q n := by
  unfold a111528
  by_cases hq : q = 0
  · subst hq
    simp only [↓reduceIte, Nat.cast_zero]
    have hsum : ∑ k ∈ Finset.Icc 1 n, a111184 n k * (0 : ℚ) ^ (k - 1) = a111184 n 1 := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro k hk hne
        have hk2 : 1 ≤ k - 1 := by simp only [Finset.mem_Icc] at hk; omega
        rw [zero_pow (by omega), mul_zero]
      · intro h1; exfalso; exact h1 (Finset.mem_Icc.mpr ⟨le_refl 1, hn⟩)
    rw [hsum]
    have h1 : a111184 n 1 = (PowerSeries.coeff (n - 1) (seriesS 0)).eval 0 := by
      rw [a111184, a111184Poly_eq_X_mul_seriesS hn, Polynomial.coeff_X_mul,
          Polynomial.coeff_zero_eq_eval_zero]
    rw [h1]
    have hW0_eval0 : evalPS 0 W0 = 1 := by
      apply PowerSeries.ext; intro m
      rw [evalPS_W0, risingSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one]
      cases m with
      | zero => simp [risingFact]
      | succ m =>
          have : risingFact (0 : ℚ) (m + 1) = 0 := by
            rw [← mul_risingFact_add_one (0 : ℚ) m, zero_mul]
          simp [this]
    have hinv0 : evalPS 0 invW0 = 1 := by
      have h := congr_arg (evalPS 0) invW0_mul_W0
      rw [map_mul, map_one, hW0_eval0, mul_one] at h
      exact h
    have hS0 : evalPS 0 (seriesS 0) = evalPS 0 (seriesZ 0) := by
      rw [seriesS, map_mul, hinv0, mul_one]
    have hcoeff := congr_arg (PowerSeries.coeff (n - 1)) hS0
    simp only [evalPS, PowerSeries.coeff_map, Polynomial.coe_evalRingHom] at hcoeff
    rw [hcoeff, coeff_seriesZ]
    simp only [Polynomial.eval_mul, Polynomial.eval_natCast]
    have hrf := map_risingFact (Polynomial.evalRingHom (0 : ℚ))
      (Polynomial.X + Polynomial.C ((0 + 1 : ℕ) : ℚ)) (n - 1)
    simp only [Polynomial.coe_evalRingHom, map_add, Polynomial.eval_X, Polynomial.eval_C,
      Nat.cast_one, zero_add] at hrf
    simp only [zero_add, Nat.cast_one]
    rw [hrf, risingFact_one]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    simp only [Nat.factorial_succ]
    push_cast
    ring
  · simp only [hq, ↓reduceIte]
    have hq_ne : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    have hev := a111184Poly_eval n hn (q : ℚ)
    have hrat : (a111184Poly n).eval (q : ℚ) =
        PowerSeries.coeff n (evalPS (q : ℚ) (ratioW 0)) := by
      rw [a111184Poly_eq_coeff_ratioW]
      simp [evalPS, PowerSeries.coeff_map]
    have hratio_eval : evalPS (q : ℚ) (ratioW 0) =
        1 + (PowerSeries.X * PowerSeries.derivative ℚ (risingSeries (q : ℚ))) *
          (risingSeries (q : ℚ))⁻¹ := by
      rw [ratioW, altA_one_eq_W0_add_X_mul_deriv, add_mul, W0_mul_invW0, map_add, map_one,
          map_mul, map_mul, evalPS_derivative, evalPS_W0, evalPS_invW0]
      simp [evalPS]
    rw [hratio_eval, map_add, PowerSeries.coeff_one] at hrat
    have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
    simp only [hn0, ↓reduceIte, zero_add] at hrat
    rw [hrat] at hev
    exact eq_div_of_mul_eq hq_ne (by linarith)

/-- Exact second-order linear ODE for `risingSeries a`:
`W' = a * W + (a + 2) * t * W' + t^2 * W''`. -/
private lemma risingSeries_ode (a : ℚ) :
    PowerSeries.derivative ℚ (risingSeries a) =
      PowerSeries.C a * risingSeries a +
      PowerSeries.C (a + 2) * PowerSeries.X * PowerSeries.derivative ℚ (risingSeries a) +
      PowerSeries.X * PowerSeries.X *
        PowerSeries.derivative ℚ (PowerSeries.derivative ℚ (risingSeries a)) := by
  apply PowerSeries.ext; intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_derivative, risingSeries, PowerSeries.coeff_mk, map_add, map_add,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, mul_assoc (PowerSeries.C (a + 2)),
          PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul, mul_zero, add_zero,
          mul_assoc PowerSeries.X, PowerSeries.coeff_zero_X_mul, add_zero]
      simp [risingFact]
  | succ n =>
      rw [PowerSeries.coeff_derivative, risingSeries, PowerSeries.coeff_mk]
      rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
      rw [mul_assoc (PowerSeries.C (a + 2)), PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
      rw [mul_assoc PowerSeries.X, PowerSeries.coeff_succ_X_mul]
      cases n with
      | zero =>
          simp only [PowerSeries.coeff_zero_X_mul, risingFact]
          push_cast; ring
      | succ n =>
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
              PowerSeries.coeff_derivative, PowerSeries.coeff_mk]
          simp only [risingFact]
          push_cast
          ring

/-- Riccati ODE for `F_a = 1 + t * W_a' * W_a⁻¹`:
`F_a - 1 = (a - 1) * t * F_a + t * F_a^2 + t^2 * F_a'`. -/
private lemma riccati_ode (a : ℚ) :
    let W := risingSeries a
    let F := 1 + PowerSeries.X * PowerSeries.derivative ℚ W * W⁻¹
    F - 1 = PowerSeries.C (a - 1) * PowerSeries.X * F +
      PowerSeries.X * (F * F) + PowerSeries.X * PowerSeries.X * PowerSeries.derivative ℚ F := by
  intro W F
  have hcW : PowerSeries.constantCoeff W = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    dsimp only [W]
    rw [risingSeries, PowerSeries.coeff_mk, risingFact]
  have hW_inv : W * W⁻¹ = 1 := PowerSeries.mul_inv_cancel W (by rw [hcW]; exact one_ne_zero)
  have hinv_W : W⁻¹ * W = 1 := by rw [mul_comm]; exact hW_inv
  have hFW : F * W = W + PowerSeries.X * PowerSeries.derivative ℚ W := by
    simp only [F, add_mul, one_mul, mul_assoc, hinv_W, mul_one]
  have hdFW := congr_arg (PowerSeries.derivative ℚ) hFW
  simp only [Derivation.leibniz, map_add, PowerSeries.derivative_X, smul_eq_mul] at hdFW
  have hode := risingSeries_ode a
  have hW_ne : IsUnit W := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hcW]
    exact isUnit_one
  apply hW_ne.mul_right_cancel
  apply hW_ne.mul_right_cancel
  set W' := PowerSeries.derivative ℚ W
  set W'' := PowerSeries.derivative ℚ W'
  set F' := PowerSeries.derivative ℚ F
  have hFW' : F * W = W + PowerSeries.X * W' := hFW
  have hWF' : W * F' = W' + W' + PowerSeries.X * W'' - F * W' := by
    have : W' * F + W * F' = W' + (PowerSeries.X * W'' + W') := by
      simpa [mul_comm] using hdFW
    linear_combination this
  have hC1 : PowerSeries.C (a - 1) = PowerSeries.C a - 1 := by rw [map_sub, map_one]
  have hC2 : PowerSeries.C (a + 2) = PowerSeries.C a + 2 := by
    have h2 : PowerSeries.C (2 : ℚ) = (2 : PowerSeries ℚ) := by
      rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]; ring
    rw [map_add, h2]
  rw [hC2] at hode
  rw [hC1]
  have hode' : W' = PowerSeries.C a * W + (PowerSeries.C a + 2) * PowerSeries.X * W' +
      PowerSeries.X * PowerSeries.X * W'' := hode
  linear_combination
    W * PowerSeries.X * hode'
    - PowerSeries.X * PowerSeries.X * W * hWF'
    - (PowerSeries.C a - 1) * PowerSeries.X * W * hFW'
    - PowerSeries.X * (F * W + W + PowerSeries.X * W') * hFW'
    - PowerSeries.X * PowerSeries.X * W' * hFW'
    + W * hFW'
    + 2 * PowerSeries.X ^ 3 * W' ^ 2 * hinv_W

/-- Proof of Conjecture 2: for `q > 0`, `(1 + t + q * t * S)' = (1 + t + q * t * S) * L'`. -/
private lemma conj2_proof (q : ℚ) (hq : 0 < q) :
    let S : PowerSeries ℚ := PowerSeries.mk fun k => if k = 0 then 0 else kurkovR k q
    let L : PowerSeries ℚ := PowerSeries.mk fun k => if k = 0 then 0 else kurkovR k q / (k : ℚ)
    let G : PowerSeries ℚ := 1 + PowerSeries.X + PowerSeries.C q * PowerSeries.X * S
    PowerSeries.derivative ℚ G = G * PowerSeries.derivative ℚ L := by
  intro S L G
  have hq_ne : q ≠ 0 := ne_of_gt hq
  -- First, relate `S` to `F_a = 1 + t * W_a' * W_a⁻¹` at `a = -1/q` with scaling `t ↦ q * t`!
  set a : ℚ := -1 / q
  have hqa : q * a = -1 := by simp only [a]; field_simp
  set W := risingSeries a
  set F := 1 + PowerSeries.X * PowerSeries.derivative ℚ W * W⁻¹
  -- Note: for `n ≥ 1`, `coeff n F = (a111184Poly n).eval a = a * ∑_{k=1}^n T(n,k) a^(k-1)`.
  have hF_coeff : ∀ n : ℕ, 0 < n → PowerSeries.coeff n F = a * (kurkovR n q / q ^ (n - 1)) := by
    intro n hn
    have hev := a111184Poly_eval n hn a
    have hrat : (a111184Poly n).eval a = PowerSeries.coeff n F := by
      have h1 : (a111184Poly n).eval a = PowerSeries.coeff n (evalPS a (ratioW 0)) := by
        rw [a111184Poly_eq_coeff_ratioW]; simp [evalPS, PowerSeries.coeff_map]
      rw [h1, ratioW, altA_one_eq_W0_add_X_mul_deriv, add_mul, W0_mul_invW0, map_add, map_one,
          map_mul, map_mul, evalPS_derivative, evalPS_W0, evalPS_invW0]
      simp [evalPS, F, W]
    rw [← hrat, hev, kurkovR]
    have hqp : q ^ (n - 1) ≠ 0 := pow_ne_zero _ hq_ne
    rw [mul_div_cancel_left₀ _ hqp]
  -- Hence `coeff n S = - q^n * coeff n F` for all `n ≥ 1`, and `0` for `n = 0`!
  have hS_coeff : ∀ n : ℕ, PowerSeries.coeff n S =
      if n = 0 then 0 else -(q ^ n) * PowerSeries.coeff n F := by
    intro n
    simp only [S, PowerSeries.coeff_mk]
    split_ifs with hn
    · rfl
    · rw [hF_coeff n (Nat.pos_of_ne_zero hn)]
      have hqn : q ^ n = q * q ^ (n - 1) := by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        simp [pow_succ']
      have hqp : q ^ (n - 1) ≠ 0 := pow_ne_zero _ hq_ne
      rw [hqn]
      calc
        kurkovR n q = -(-1) * kurkovR n q := by ring
        _ = -(q * a) * kurkovR n q := by rw [hqa]
        _ = -(q * q ^ (n - 1)) * (a * (kurkovR n q / q ^ (n - 1))) := by
            field_simp [hqp]
  -- Also `PowerSeries.X * L' = S`!
  have hXL' : PowerSeries.X * PowerSeries.derivative ℚ L = S := by
    apply PowerSeries.ext; intro n
    cases n with
    | zero =>
        simp [S, PowerSeries.coeff_zero_X_mul]
    | succ n =>
        rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
        simp only [L, S, PowerSeries.coeff_mk, Nat.succ_ne_zero, ↓reduceIte]
        have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        field_simp [hn1]
        push_cast; ring
  -- So it suffices to prove `X * G' = G * S` (since multiplying by `X` is injective on `PowerSeries ℚ`)!
  have hXG' : PowerSeries.X * PowerSeries.derivative ℚ G = G * S := by
    have hric : F - 1 = PowerSeries.C (a - 1) * PowerSeries.X * F +
        PowerSeries.X * (F * F) + PowerSeries.X * PowerSeries.X * PowerSeries.derivative ℚ F :=
      riccati_ode a
    have hF0 : PowerSeries.coeff 0 F = 1 := by
      simp [F, mul_assoc]
    set Fq : PowerSeries ℚ := PowerSeries.mk fun k => q ^ k * PowerSeries.coeff k F
    have hS_eq_Fq : S = 1 - Fq := by
      apply PowerSeries.ext; intro k
      rw [hS_coeff k, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_mk]
      split_ifs with hk
      · subst hk; simp [hF0]
      · ring
    have hFq_mul : ∀ n : ℕ, PowerSeries.coeff n (Fq * Fq) = q ^ n * PowerSeries.coeff n (F * F) := by
      intro n
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      have hadd : p.1 + p.2 = n := by simpa using hp
      rw [← hadd, pow_add]; ring
    apply PowerSeries.ext; intro n
    cases n with
    | zero =>
        rw [PowerSeries.coeff_zero_X_mul, ps_coeff_zero_mul]
        simp [S]
    | succ n =>
        have hric_n := congr_arg (PowerSeries.coeff (n + 1)) hric
        rw [map_sub, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), sub_zero] at hric_n
        conv_rhs at hric_n =>
          rw [map_add, map_add, mul_assoc (PowerSeries.C (a - 1)), PowerSeries.coeff_C_mul,
              PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
              mul_assoc PowerSeries.X, PowerSeries.coeff_succ_X_mul]
        have hlhs : PowerSeries.coeff (n + 1) (PowerSeries.X * PowerSeries.derivative ℚ G) =
            ((n + 1 : ℕ) : ℚ) * (if n = 0 then 1 else 0) +
              ((n + 1 : ℕ) : ℚ) * q * PowerSeries.coeff n S := by
          rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
          simp only [G, map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte, zero_add,
            PowerSeries.coeff_X, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
          have h1 : (if n + 1 = 1 then (1 : ℚ) else 0) = if n = 0 then 1 else 0 := by
            by_cases hn0 : n = 0 <;> simp [hn0]
          rw [h1]; push_cast; ring
        have hrhs : PowerSeries.coeff (n + 1) (G * S) =
            PowerSeries.coeff (n + 1) S + PowerSeries.coeff n S +
              q * PowerSeries.coeff n (S * S) := by
          have hGS : G * S = S + PowerSeries.X * S + PowerSeries.C q * (PowerSeries.X * (S * S)) := by
            simp only [G]; ring
          rw [hGS, map_add, map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
              PowerSeries.coeff_succ_X_mul]
        rw [hlhs, hrhs]
        have hSS : PowerSeries.coeff n (S * S) =
            q ^ n * (PowerSeries.coeff n (F * F) - 2 * PowerSeries.coeff n F +
              if n = 0 then 1 else 0) := by
          have hsq : S * S = 1 - PowerSeries.C 2 * Fq + Fq * Fq := by
            rw [hS_eq_Fq]
            have h2 : PowerSeries.C (2 : ℚ) = (2 : PowerSeries ℚ) := by
              rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one]; ring
            rw [h2]; ring
          rw [hsq, map_add, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
              PowerSeries.coeff_mk, hFq_mul n]
          split_ifs with hn0
          · subst hn0; simp; ring
          · ring
        rw [hSS, hS_coeff (n + 1), hS_coeff n]
        simp only [Nat.succ_ne_zero, ↓reduceIte]
        cases n with
        | zero =>
            rw [PowerSeries.coeff_zero_X_mul, ps_coeff_zero_mul, hF0] at hric_n
            simp only [↓reduceIte, pow_zero, mul_zero, add_zero, one_mul,
              ps_coeff_zero_mul, hF0] at hric_n ⊢
            rw [hric_n]
            simp only [a]
            field_simp [hq_ne]
            ring
        | succ n =>
            rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative] at hric_n
            simp only [Nat.succ_ne_zero, ↓reduceIte] at hric_n ⊢
            rw [hric_n]
            have hqn : q ^ (n + 2) = q * q ^ (n + 1) := by ring
            rw [hqn]
            simp only [a]
            push_cast
            field_simp [hq_ne]
            ring
  -- Cancel `PowerSeries.X` from `X * G' = G * S = X * (G * L')`!
  apply PowerSeries.ext; intro n
  have h := congr_arg (PowerSeries.coeff (n + 1)) hXG'
  rw [PowerSeries.coeff_succ_X_mul] at h
  have h2 : G * S = PowerSeries.X * (G * PowerSeries.derivative ℚ L) := by
    rw [← hXL']; ring
  rw [h2, PowerSeries.coeff_succ_X_mul] at h
  exact h

theorem main_proof :
    (∀ n : ℕ, 0 < n → ∀ q : ℕ,
      ∑ k ∈ Finset.Icc 1 n, a111184 n k * (q : ℚ) ^ (k - 1) = a111528 q n) ∧
    (∀ q : ℚ, 0 < q →
      let S : PowerSeries ℚ := PowerSeries.mk fun k => if k = 0 then 0 else kurkovR k q
      let L : PowerSeries ℚ := PowerSeries.mk fun k => if k = 0 then 0 else kurkovR k q / (k : ℚ)
      let G : PowerSeries ℚ := 1 + PowerSeries.X + PowerSeries.C q * PowerSeries.X * S
      PowerSeries.derivative ℚ G = G * PowerSeries.derivative ℚ L) ∧
    (∀ n m : ℕ, 0 < n → n ≤ m →
      a111184Poly n = Polynomial.X * kurkovVec m (n - 1)) :=
  ⟨conj1_proof, conj2_proof, conj3_proof⟩

end OMA.S_oeis_a111184

theorem OMA.solution : type_of% @OMA.S_oeis_a111184.main :=
  OMA.S_oeis_a111184.main_proof
