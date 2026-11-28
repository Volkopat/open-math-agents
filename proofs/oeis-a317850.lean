import OMAStatements.S_oeis_a317850
import Mathlib

namespace OMA.A317850Proof

/-- `gfun a = (a ^ 4 + 1) ^ 4 + 1 - a`: its roots modulo `10 ^ k` give the pairs `x = a`, `y = a ^ 4 + 1` at `n = 4`. -/
def gfun (a : ℤ) : ℤ := (a ^ 4 + 1) ^ 4 + 1 - a

/-- The derivative of `gfun`. -/
def dfun (a : ℤ) : ℤ := 16 * (a ^ 4 + 1) ^ 3 * a ^ 3 - 1

/-- The second order remainder in the expansion of `gfun (a + h)`. -/
def qfun (a h : ℤ) : ℤ :=
  4 * (a ^ 4 + 1) ^ 3 * (6 * a ^ 2 + 4 * a * h + h ^ 2)
    + 6 * (a ^ 4 + 1) ^ 2 * (4 * a ^ 3 + h * (6 * a ^ 2 + 4 * a * h + h ^ 2)) ^ 2
    + 4 * (a ^ 4 + 1) * h * (4 * a ^ 3 + h * (6 * a ^ 2 + 4 * a * h + h ^ 2)) ^ 3
    + h ^ 2 * (4 * a ^ 3 + h * (6 * a ^ 2 + 4 * a * h + h ^ 2)) ^ 4

set_option maxHeartbeats 1000000 in
/-- Exact Taylor expansion of `gfun` to second order. -/
theorem taylor (a h : ℤ) : gfun (a + h) = gfun a + h * dfun a + h ^ 2 * qfun a h := by
  unfold gfun dfun qfun
  ring

/-- If `a ≡ 2 (mod 10)` then `1 + 3 * dfun a ≡ 0 (mod 10)` (here `dfun 2 = 628863`), so `3` inverts `-dfun a`. -/
theorem dfun_unit (a : ℤ) (h : (10 : ℤ) ∣ a - 2) : (10 : ℤ) ∣ 1 + 3 * dfun a := by
  have ha : a ≡ 2 [ZMOD 10] := (Int.modEq_iff_dvd.mpr h).symm
  have h1 : 1 + 3 * dfun a ≡ 1 + 3 * dfun 2 [ZMOD 10] := by
    unfold dfun
    first
    | exact Int.ModEq.add_left 1 (Int.ModEq.mul_left 3 (Int.ModEq.sub_right 1
        (Int.ModEq.mul (Int.ModEq.mul_left 16 (Int.ModEq.pow 3 (Int.ModEq.add_right 1 (Int.ModEq.pow 4 ha))))
          (Int.ModEq.pow 3 ha))))
    | gcongr
  have h2 : 1 + 3 * dfun 2 ≡ 0 [ZMOD 10] := by
    unfold dfun
    first
    | decide
    | rfl
    | (unfold Int.ModEq; norm_num)
  exact Int.modEq_zero_iff_dvd.mp (h1.trans h2)

/-- The lifting sequence: `aSeq 0 = 2` and `aSeq (k + 1) = aSeq k + 3 * gfun (aSeq k)`. -/
def aSeq : ℕ → ℤ
  | 0 => 2
  | k + 1 => aSeq k + 3 * gfun (aSeq k)

/-- `aSeq k` is a root of `gfun` modulo `10 ^ (k + 1)` and is `≡ 2 (mod 10)`. -/
theorem aSeq_spec (k : ℕ) : (10 : ℤ) ^ (k + 1) ∣ gfun (aSeq k) ∧ (10 : ℤ) ∣ aSeq k - 2 := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (10 : ℤ) ^ (0 + 1) ∣ ((2 : ℤ) ^ 4 + 1) ^ 4 + 1 - 2
      first
      | norm_num
      | decide
    · show (10 : ℤ) ∣ (2 : ℤ) - 2
      first
      | norm_num
      | decide
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have h10 : (10 : ℤ) ∣ gfun (aSeq k) := dvd_trans (dvd_pow_self (10 : ℤ) (Nat.succ_ne_zero k)) h1
    have e1 : aSeq (k + 1) = aSeq k + 3 * gfun (aSeq k) := rfl
    have hD := dfun_unit (aSeq k) h2
    refine ⟨?_, ?_⟩
    · rw [e1, taylor]
      have e : gfun (aSeq k) + 3 * gfun (aSeq k) * dfun (aSeq k)
            + (3 * gfun (aSeq k)) ^ 2 * qfun (aSeq k) (3 * gfun (aSeq k))
          = gfun (aSeq k) * (1 + 3 * dfun (aSeq k))
            + gfun (aSeq k) * gfun (aSeq k) * (9 * qfun (aSeq k) (3 * gfun (aSeq k))) := by
        ring
      rw [e, pow_succ]
      exact dvd_add (mul_dvd_mul h1 hD) (dvd_mul_of_dvd_left (mul_dvd_mul h1 h10) _)
    · rw [e1]
      have e : aSeq k + 3 * gfun (aSeq k) - 2 = (aSeq k - 2) + 3 * gfun (aSeq k) := by ring
      rw [e]
      exact dvd_add h2 (dvd_mul_of_dvd_right h10 3)

/-- The 10-adic integer `x`, level `k`. -/
def xs (k : ℕ) : ZMod (10 ^ k) := ((aSeq k : ℤ) : ZMod (10 ^ k))

/-- The 10-adic integer `y = x ^ 4 + 1`, level `k`. -/
def ys (k : ℕ) : ZMod (10 ^ k) := xs k ^ 4 + 1

theorem xs_compat : OMA.S_oeis_a317850.IsTenAdic xs := by
  unfold OMA.S_oeis_a317850.IsTenAdic
  intro k
  have h1 := (aSeq_spec k).1
  have hd : (10 : ℤ) ^ k ∣ aSeq k - aSeq (k + 1) := by
    have e : aSeq k - aSeq (k + 1) = -(3 * gfun (aSeq k)) := by
      show aSeq k - (aSeq k + 3 * gfun (aSeq k)) = -(3 * gfun (aSeq k))
      ring
    rw [e, dvd_neg]
    exact dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow (10 : ℤ) (Nat.le_succ k)) h1) 3
  unfold xs
  rw [map_intCast]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (by exact_mod_cast hd)

theorem ys_compat : OMA.S_oeis_a317850.IsTenAdic ys := by
  have hx := xs_compat
  unfold OMA.S_oeis_a317850.IsTenAdic at hx ⊢
  intro k
  unfold ys
  rw [map_add, map_pow, map_one, hx k]

theorem xy_eq (k : ℕ) : xs k ^ 4 + 1 = ys k ∧ ys k ^ 4 + 1 = xs k := by
  refine ⟨rfl, ?_⟩
  have h1 : (10 : ℤ) ^ k ∣ gfun (aSeq k) :=
    dvd_trans (pow_dvd_pow (10 : ℤ) (Nat.le_succ k)) (aSeq_spec k).1
  have hz : ((gfun (aSeq k) : ℤ) : ZMod (10 ^ k)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast h1)
  unfold gfun at hz
  push_cast at hz
  unfold ys xs
  first
  | exact sub_eq_zero.mp hz
  | linear_combination hz

end OMA.A317850Proof

/-- The conjecture fails at `n = 4`: `x = ...492162`, `y = x ^ 4 + 1 = ...851537` is a pair of 10-adic integers with
`x ^ 4 + 1 = y` and `y ^ 4 + 1 = x`, while `4 % 20 = 4`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a317850.main) := by
  intro h
  have h4 := (h 4 (by norm_num)).mp
    ⟨OMA.A317850Proof.xs, OMA.A317850Proof.ys, OMA.A317850Proof.xs_compat, OMA.A317850Proof.ys_compat,
      OMA.A317850Proof.xy_eq⟩
  first
  | omega
  | (revert h4; decide)
  | simp at h4
