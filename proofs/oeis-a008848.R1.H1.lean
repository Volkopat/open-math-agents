import OMAReductions.R_oeis_a008848_R1
import Mathlib

/-!
# Proof of `oeis-a008848.R1.H1`

Shows that `x = 81 = 3^4` is the only prime power `x = p^k` that is a perfect square whose
sum of divisors `σ(x)` is also a perfect square.

Writing `x = p^(2j)` (`j ≥ 1`) and `σ(x) = y^2`, the geometric-series identity gives the
generalized Pell equation `p * (p^j)^2 - (p - 1) * y^2 = 1`. Using the primality of the base `p`,
an elementary descent parametrizes all positive solutions as odd powers `(√p + √(p - 1))^(2h+1)`,
binomial congruences mod `p` and mod `p^2` rule out all primes `p ≥ 5`, and `p = 3` is settled
directly via `U_3 = 9` and `U_9 = 8721 = 27 * 17 * 19`.
-/

namespace OMA.OeisA008848H1

open ArithmeticFunction Finset BigOperators

/-- Real evaluation `u * √p + v * √(p - 1)` of a pair `(u, v)`. -/
noncomputable def eval (p u v : ℕ) : ℝ :=
  (u : ℝ) * Real.sqrt (p : ℝ) + (v : ℝ) * Real.sqrt ((p - 1 : ℕ) : ℝ)

/-- Uniqueness of `(u, v)` from `u * √p + v * √(p - 1)` for a prime `p`. -/
lemma eval_injective {p : ℕ} (hp : p.Prime) {u₁ v₁ u₂ v₂ : ℕ}
    (heq : eval p u₁ v₁ = eval p u₂ v₂) : u₁ = u₂ ∧ v₁ = v₂ := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hsq : ((u₁ : ℤ) - (u₂ : ℤ)) ^ 2 * (p : ℤ) = ((v₂ : ℤ) - (v₁ : ℤ)) ^ 2 * ((p - 1 : ℕ) : ℤ) := by
    have hreal : (((u₁ : ℤ) - (u₂ : ℤ)) : ℝ) * Real.sqrt (p : ℝ) =
        (((v₂ : ℤ) - (v₁ : ℤ)) : ℝ) * Real.sqrt ((p - 1 : ℕ) : ℝ) := by
      unfold eval at heq
      push_cast
      linarith
    have hsq_real : ((((u₁ : ℤ) - (u₂ : ℤ)) : ℝ) * Real.sqrt (p : ℝ)) ^ 2 =
        ((((v₂ : ℤ) - (v₁ : ℤ)) : ℝ) * Real.sqrt ((p - 1 : ℕ) : ℝ)) ^ 2 := by
      rw [hreal]
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg p), Real.sq_sqrt (Nat.cast_nonneg (p - 1))] at hsq_real
    exact_mod_cast hsq_real
  have hnat : ((u₁ : ℤ) - (u₂ : ℤ)).natAbs ^ 2 * p = ((v₂ : ℤ) - (v₁ : ℤ)).natAbs ^ 2 * (p - 1) := by
    have h1 : (((((u₁ : ℤ) - (u₂ : ℤ)).natAbs ^ 2 * p : ℕ) : ℤ)) =
        (((((v₂ : ℤ) - (v₁ : ℤ)).natAbs ^ 2 * (p - 1) : ℕ) : ℤ)) := by
      push_cast
      rw [sq_abs, sq_abs]
      exact hsq
    exact_mod_cast h1
  set a := ((u₁ : ℤ) - (u₂ : ℤ)).natAbs with ha_def
  set b := ((v₂ : ℤ) - (v₁ : ℤ)).natAbs with hb_def
  have ha0 : a = 0 := by
    by_contra hne
    have hpos : 0 < a ^ 2 * p := Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero hne) 2) hp.pos
    have hbne : b ≠ 0 := by
      intro hb0
      rw [hb0] at hnat
      simp at hnat
      omega
    have hcop : ¬ p ∣ (p - 1) := by
      intro hdvd
      have hle : p ≤ p - 1 := Nat.le_of_dvd (by omega) hdvd
      omega
    have hval1 : padicValNat p (a ^ 2 * p) = 2 * padicValNat p a + 1 := by
      rw [padicValNat.mul (pow_ne_zero 2 hne) hp.ne_zero, sq, padicValNat.mul hne hne, padicValNat.self hp.one_lt]
      omega
    have hval2 : padicValNat p (b ^ 2 * (p - 1)) = 2 * padicValNat p b := by
      rw [padicValNat.mul (pow_ne_zero 2 hbne) (by omega), sq, padicValNat.mul hbne hbne,
        padicValNat.eq_zero_of_not_dvd hcop, add_zero]
      omega
    rw [hnat] at hval1
    omega
  have hb0 : b = 0 := by
    rw [ha0] at hnat
    simp at hnat
    rcases hnat with h | h
    · exact h
    · omega
  have hu : (u₁ : ℤ) - (u₂ : ℤ) = 0 := Int.natAbs_eq_zero.mp ha0
  have hv : (v₂ : ℤ) - (v₁ : ℤ) = 0 := Int.natAbs_eq_zero.mp hb0
  exact ⟨by omega, by omega⟩

/-- Recursive odd powers `(√p + √(p - 1))^(2h + 1)`. -/
def recUV (p : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | h + 1 =>
    let (u, v) := recUV p h
    ((2 * p - 1) * u + 2 * (p - 1) * v, 2 * p * u + (2 * p - 1) * v)

lemma eval_recUV {p : ℕ} (hp : 1 ≤ p) (h : ℕ) :
    eval p (recUV p h).1 (recUV p h).2 =
      (Real.sqrt (p : ℝ) + Real.sqrt ((p - 1 : ℕ) : ℝ)) ^ (2 * h + 1) := by
  induction h with
  | zero =>
    simp [recUV, eval]
  | succ h ih =>
    have hpow : (Real.sqrt (p : ℝ) + Real.sqrt ((p - 1 : ℕ) : ℝ)) ^ (2 * (h + 1) + 1) =
        (Real.sqrt (p : ℝ) + Real.sqrt ((p - 1 : ℕ) : ℝ)) ^ (2 * h + 1) *
          (Real.sqrt (p : ℝ) + Real.sqrt ((p - 1 : ℕ) : ℝ)) ^ 2 := by
      rw [show 2 * (h + 1) + 1 = (2 * h + 1) + 2 by omega, pow_add]
    rw [hpow, ← ih]
    simp only [recUV, eval]
    have hsp : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
    have hsp1 : Real.sqrt ((p - 1 : ℕ) : ℝ) ^ 2 = ((p - 1 : ℕ) : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg (p - 1))
    have hcast1 : ((2 * p - 1 : ℕ) : ℝ) = (p : ℝ) + ((p - 1 : ℕ) : ℝ) := by
      have : 2 * p - 1 = p + (p - 1) := by omega
      rw [this]; push_cast; ring
    push_cast
    rw [hcast1]
    set sp := Real.sqrt (p : ℝ)
    set sp1 := Real.sqrt ((p - 1 : ℕ) : ℝ)
    rw [← hsp, ← hsp1]
    ring

/-- Binomial formula for the `√p` coordinate of `(a √p + b √(p - 1))^(2h + 1)`. -/
def oddU (p a b h : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (h + 1),
    (2 * h + 1).choose (2 * r + 1) * a ^ (2 * r + 1) * b ^ (2 * (h - r)) * p ^ r * (p - 1) ^ (h - r)

/-- Binomial formula for the `√(p - 1)` coordinate of `(a √p + b √(p - 1))^(2h + 1)`. -/
def oddV (p a b h : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (h + 1),
    (2 * h + 1).choose (2 * r) * a ^ (2 * r) * b ^ (2 * (h - r) + 1) * p ^ r * (p - 1) ^ (h - r)

lemma eval_oddUV (p a b h : ℕ) :
    eval p (oddU p a b h) (oddV p a b h) =
      ((a : ℝ) * Real.sqrt (p : ℝ) + (b : ℝ) * Real.sqrt ((p - 1 : ℕ) : ℝ)) ^ (2 * h + 1) := by
  rw [add_pow]
  have hsp : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
  have hsp1 : Real.sqrt ((p - 1 : ℕ) : ℝ) ^ 2 = ((p - 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg (p - 1))
  have hsplit : ∀ f : ℕ → ℝ,
      ∑ k ∈ Finset.range (2 * h + 2), f k =
        (∑ r ∈ Finset.range (h + 1), f (2 * r + 1)) +
        (∑ r ∈ Finset.range (h + 1), f (2 * r)) := by
    intro f
    induction h with
    | zero =>
      simp [Finset.sum_range_succ]; ring
    | succ h ih =>
      rw [show 2 * (h + 1) + 2 = (2 * h + 2) + 2 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ (n := h + 1), Finset.sum_range_succ (n := h + 1)]
      have h1 : 2 * h + 2 = 2 * (h + 1) := by omega
      have h2 : 2 * h + 2 + 1 = 2 * (h + 1) + 1 := by omega
      rw [h1, h2]
      ring
  rw [show 2 * h + 1 + 1 = 2 * h + 2 by omega, hsplit]
  unfold eval oddU oddV
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun r hr => ?_
    have hrle : r ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hsub : 2 * h - 2 * r = 2 * (h - r) := by omega
    rw [hsub, mul_pow, mul_pow, pow_succ (Real.sqrt (p : ℝ)),
      pow_mul (Real.sqrt (p : ℝ)) 2 r, hsp,
      pow_mul (Real.sqrt ((p - 1 : ℕ) : ℝ)) 2 (h - r), hsp1]
    ring
  · refine Finset.sum_congr rfl fun r hr => ?_
    have hrle : r ≤ h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hsub : 2 * h + 1 - 2 * r = 2 * (h - r) + 1 := by omega
    rw [hsub, mul_pow, mul_pow,
      pow_mul (Real.sqrt (p : ℝ)) 2 r, hsp,
      pow_succ (Real.sqrt ((p - 1 : ℕ) : ℝ)),
      pow_mul (Real.sqrt ((p - 1 : ℕ) : ℝ)) 2 (h - r), hsp1]
    ring

lemma recUV_eq_oddUV {p : ℕ} (hp : p.Prime) (h : ℕ) :
    (recUV p h).1 = oddU p 1 1 h ∧ (recUV p h).2 = oddV p 1 1 h := by
  apply eval_injective hp
  rw [eval_recUV hp.one_lt.le, eval_oddUV]
  simp

lemma oddU_dvd_self (p a b h : ℕ) : a ∣ oddU p a b h := by
  unfold oddU
  refine Finset.dvd_sum fun r _ => ?_
  have hd : a ∣ a ^ (2 * r + 1) := by
    rw [pow_succ]; exact dvd_mul_left a _
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _) _) _

lemma oddU_dvd_of_dvd {p : ℕ} (hp : p.Prime) {h₁ h₂ : ℕ} :
    oddU p 1 1 h₁ ∣ oddU p 1 1 (2 * h₁ * h₂ + h₁ + h₂) := by
  have heq : oddU p 1 1 (2 * h₁ * h₂ + h₁ + h₂) =
      oddU p (oddU p 1 1 h₁) (oddV p 1 1 h₁) h₂ := by
    refine (eval_injective hp (v₁ := oddV p 1 1 (2 * h₁ * h₂ + h₁ + h₂))
      (v₂ := oddV p (oddU p 1 1 h₁) (oddV p 1 1 h₁) h₂) ?_).1
    rw [eval_oddUV, eval_oddUV]
    change _ = (eval p (oddU p 1 1 h₁) (oddV p 1 1 h₁)) ^ (2 * h₂ + 1)
    rw [eval_oddUV]
    simp only [Nat.cast_one, one_mul, ← pow_mul]
    congr 1
    ring
  rw [heq]
  exact oddU_dvd_self p _ _ _

/-- Elementary descent parametrizing all positive solutions of `p u^2 = (p - 1) y^2 + 1`. -/
lemma pell_param {p : ℕ} (hp : 3 ≤ p) :
    ∀ u y : ℕ, 0 < u → 0 < y → p * u ^ 2 = (p - 1) * y ^ 2 + 1 →
      ∃ h : ℕ, u = (recUV p h).1 ∧ y = (recUV p h).2 := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro y hu hy hpell
    by_cases hu1 : u = 1
    · subst hu1
      have hy1 : y = 1 := by
        simp only [one_pow, mul_one] at hpell
        have h1 : (p - 1) * y ^ 2 = (p - 1) * 1 := by omega
        have h2 : y ^ 2 = 1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p - 1) h1
        nlinarith
      exact ⟨0, rfl, hy1⟩
    · have hu2 : 2 ≤ u := by omega
      have hy_gt_u : u < y := by
        by_contra! hle
        have : (p - 1) * y ^ 2 ≤ (p - 1) * u ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle 2)
        have h1 : p * u ^ 2 = (p - 1) * u ^ 2 + u ^ 2 := by
          have : p = (p - 1) + 1 := by omega
          nlinarith
        nlinarith
      set d : ℕ := y - u with hd_def
      have hd_pos : 0 < d := by omega
      have hy_eq : y = u + d := by omega
      have hu_mul : (u : ℤ) * ((u : ℤ) - 2 * ((p - 1 : ℕ) : ℤ) * (d : ℤ)) =
          1 + ((p - 1 : ℕ) : ℤ) * (d : ℤ) ^ 2 := by
        have hp_int : (p : ℤ) * (u : ℤ) ^ 2 = ((p - 1 : ℕ) : ℤ) * ((u : ℤ) + (d : ℤ)) ^ 2 + 1 := by
          have : p * u ^ 2 = (p - 1) * (u + d) ^ 2 + 1 := by rw [← hy_eq]; exact hpell
          exact_mod_cast this
        have hp_sub : (p : ℤ) = ((p - 1 : ℕ) : ℤ) + 1 := by omega
        nlinarith
      have hu'_pos_int : 0 < (u : ℤ) - 2 * ((p - 1 : ℕ) : ℤ) * (d : ℤ) := by
        nlinarith [sq_nonneg (d : ℤ)]
      have h2pd_lt_u : 2 * (p - 1) * d < u := by
        have hcast : ((2 * (p - 1) * d : ℕ) : ℤ) < (u : ℤ) := by push_cast; linarith
        exact_mod_cast hcast
      set u' : ℕ := u - 2 * (p - 1) * d with hu'_def
      have hu'_pos : 0 < u' := by omega
      have hu'_lt_u : u' < u := by
        have : 0 < 2 * (p - 1) * d := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hd_pos
        omega
      have hu'_lt_d : u' < d := by
        have h1 : (u : ℤ) * (u' : ℤ) = 1 + ((p - 1 : ℕ) : ℤ) * (d : ℤ) ^ 2 := by
          have hu'_cast : (u' : ℤ) = (u : ℤ) - 2 * ((p - 1 : ℕ) : ℤ) * (d : ℤ) := by
            dsimp [u']; rw [Nat.cast_sub h2pd_lt_u.le]; push_cast; ring
          rw [hu'_cast]; exact hu_mul
        have h2 : (1 : ℤ) + ((p - 1 : ℕ) : ℤ) * (d : ℤ) ^ 2 < 2 * ((p - 1 : ℕ) : ℤ) * (d : ℤ) ^ 2 := by
          have hp2 : (2 : ℤ) ≤ ((p - 1 : ℕ) : ℤ) := by omega
          have hd1 : (1 : ℤ) ≤ (d : ℤ) ^ 2 := by nlinarith
          nlinarith
        have h3 : 2 * ((p - 1 : ℕ) : ℤ) * (d : ℤ) ^ 2 < (u : ℤ) * (d : ℤ) := by
          have h2' : 2 * ((p - 1 : ℕ) : ℤ) * (d : ℤ) < (u : ℤ) := by omega
          nlinarith
        have h4 : (u : ℤ) * (u' : ℤ) < (u : ℤ) * (d : ℤ) := by linarith
        nlinarith
      set y' : ℕ := d - u' with hy'_def
      have hy'_pos : 0 < y' := by omega
      have hd_eq : d = u' + y' := by omega
      have hu_rec : u = (2 * p - 1) * u' + 2 * (p - 1) * y' := by
        have h1 : u = u' + 2 * (p - 1) * d := by omega
        have h2 : 2 * p - 1 = 1 + 2 * (p - 1) := by omega
        calc u = u' + 2 * (p - 1) * (u' + y') := by rw [h1, hd_eq]
          _ = (1 + 2 * (p - 1)) * u' + 2 * (p - 1) * y' := by ring
          _ = (2 * p - 1) * u' + 2 * (p - 1) * y' := by rw [← h2]
      have hy_rec : y = 2 * p * u' + (2 * p - 1) * y' := by
        have h2p : 2 * p = (2 * p - 1) + 1 := by omega
        have h2p1 : 2 * p - 1 = 2 * (p - 1) + 1 := by omega
        calc y = ((2 * p - 1) * u' + 2 * (p - 1) * y') + (u' + y') := by rw [hy_eq, hu_rec, hd_eq]
          _ = ((2 * p - 1) + 1) * u' + (2 * (p - 1) + 1) * y' := by ring
          _ = 2 * p * u' + (2 * p - 1) * y' := by rw [← h2p, ← h2p1]
      have hpell' : p * u' ^ 2 = (p - 1) * y' ^ 2 + 1 := by
        have h1 : (p : ℤ) * (u : ℤ) ^ 2 = ((p - 1 : ℕ) : ℤ) * (y : ℤ) ^ 2 + 1 := by exact_mod_cast hpell
        have hu_z : (u : ℤ) = (2 * (p : ℤ) - 1) * (u' : ℤ) + 2 * ((p - 1 : ℕ) : ℤ) * (y' : ℤ) := by
          have h2p : ((2 * p - 1 : ℕ) : ℤ) = 2 * (p : ℤ) - 1 := by omega
          have := congrArg (Nat.cast (R := ℤ)) hu_rec
          push_cast at this
          rw [h2p] at this
          exact this
        have hy_z : (y : ℤ) = 2 * (p : ℤ) * (u' : ℤ) + (2 * (p : ℤ) - 1) * (y' : ℤ) := by
          have h2p : ((2 * p - 1 : ℕ) : ℤ) = 2 * (p : ℤ) - 1 := by omega
          have := congrArg (Nat.cast (R := ℤ)) hy_rec
          push_cast at this
          rw [h2p] at this
          exact this
        have hp_sub : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
        have hident : (p : ℤ) * (u : ℤ) ^ 2 - ((p - 1 : ℕ) : ℤ) * (y : ℤ) ^ 2 =
            (p : ℤ) * (u' : ℤ) ^ 2 - ((p - 1 : ℕ) : ℤ) * (y' : ℤ) ^ 2 := by
          rw [hu_z, hy_z, hp_sub]; ring
        have hres : (p : ℤ) * (u' : ℤ) ^ 2 = ((p - 1 : ℕ) : ℤ) * (y' : ℤ) ^ 2 + 1 := by linarith
        exact_mod_cast hres
      obtain ⟨h, hu', hy'⟩ := ih u' hu'_lt_u y' hu'_pos hy'_pos hpell'
      exact ⟨h + 1, by rw [hu_rec, hu', hy']; rfl, by rw [hy_rec, hu', hy']; rfl⟩

/-- Congruence `oddU p 1 1 h ≡ (2h + 1) * (p - 1)^h (mod p)`. -/
lemma oddU_mod_p (p h : ℕ) :
    oddU p 1 1 h ≡ (2 * h + 1) * (p - 1) ^ h [MOD p] := by
  unfold oddU
  rw [Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, Nat.sub_zero, mul_zero, zero_add, Nat.choose_one_right]
  have hdvd : p ∣ ∑ r ∈ Finset.range h,
      (2 * h + 1).choose (2 * (r + 1) + 1) * p ^ (r + 1) * (p - 1) ^ (h - (r + 1)) := by
    refine Finset.dvd_sum fun r _ => ?_
    have hp1 : p ∣ p ^ (r + 1) := by rw [pow_succ]; exact dvd_mul_left p _
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp1 _) _
  obtain ⟨k, hk⟩ := hdvd
  rw [hk]
  exact Nat.ModEq.add_left_cancel' 0 (by simp [Nat.ModEq, Nat.add_mod])

lemma prime_dvd_oddU_iff {p : ℕ} (hp : p.Prime) (h : ℕ) :
    p ∣ oddU p 1 1 h ↔ p ∣ (2 * h + 1) := by
  have hmod := oddU_mod_p p h
  rw [Nat.ModEq.dvd_iff hmod dvd_rfl, hp.dvd_mul]
  have hcop : ¬ p ∣ (p - 1) ^ h := by
    intro hd
    have hp2 := hp.two_le
    have h1 : p ∣ p - 1 := hp.dvd_of_dvd_pow hd
    have hle : p ≤ p - 1 := Nat.le_of_dvd (by omega) h1
    omega
  simp [hcop]

/-- Lower bound `oddU p 1 1 h ≥ (2h + 1) * (p - 1)^h`. -/
lemma oddU_ge_first_term (p h : ℕ) :
    (2 * h + 1) * (p - 1) ^ h ≤ oddU p 1 1 h := by
  unfold oddU
  have h0 : 0 ∈ Finset.range (h + 1) := Finset.mem_range.mpr (Nat.succ_pos h)
  have hle := Finset.single_le_sum (f := fun r =>
    (2 * h + 1).choose (2 * r + 1) * 1 ^ (2 * r + 1) * 1 ^ (2 * (h - r)) * p ^ r * (p - 1) ^ (h - r))
    (fun _ _ => Nat.zero_le _) h0
  simpa [Nat.choose_one_right] using hle

/-- For prime `p ≥ 5`, `oddU p 1 1 ((p - 1) / 2)` is divisible by `p` but NOT by `p^2`. -/
lemma not_prime_sq_dvd_oddU_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ oddU p 1 1 ((p - 1) / 2) := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  set h := (p - 1) / 2 with hh_def
  have h2h : 2 * h + 1 = p := by omega
  have hh2 : 2 ≤ h := by omega
  unfold oddU
  rw [show h + 1 = (h - 1) + 2 by omega, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.choose_one_right, one_pow, mul_one, pow_zero, Nat.sub_zero, pow_one, h2h]
  -- r = 1 term: p.choose 3 * p * (p - 1)^(h - 1), divisible by p^2 since p ∣ p.choose 3
  have hdvd1 : p ^ 2 ∣ p.choose 3 * p * (p - 1) ^ (h - 1) := by
    have hc : p ∣ p.choose 3 := hp.dvd_choose_self (by omega) (by omega)
    obtain ⟨c, hc⟩ := hc
    rw [hc, sq]
    exact ⟨c * (p - 1) ^ (h - 1), by ring⟩
  -- r ≥ 2 terms: each contains p^(r + 2) which is divisible by p^2
  have hdvd_tail : p ^ 2 ∣ ∑ r ∈ Finset.range (h - 1),
      p.choose (2 * (r + 1 + 1) + 1) * p ^ (r + 1 + 1) * (p - 1) ^ (h - (r + 1 + 1)) := by
    refine Finset.dvd_sum fun r _ => ?_
    have hp2 : p ^ 2 ∣ p ^ (r + 1 + 1) := by
      rw [show r + 1 + 1 = r + 2 by omega, pow_add]; exact dvd_mul_left _ _
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp2 _) _
  intro hdiv
  have hsum_dvd : p ^ 2 ∣ p * (p - 1) ^ h := by
    have h1 := dvd_add hdvd_tail hdvd1
    have h2 : (∑ r ∈ Finset.range (h - 1),
        p.choose (2 * (r + 1 + 1) + 1) * p ^ (r + 1 + 1) * (p - 1) ^ (h - (r + 1 + 1))) +
        p.choose 3 * p * (p - 1) ^ (h - 1) + p * (p - 1) ^ h =
        ((∑ r ∈ Finset.range (h - 1),
          p.choose (2 * (r + 1 + 1) + 1) * p ^ (r + 1 + 1) * (p - 1) ^ (h - (r + 1 + 1))) +
          p.choose 3 * p * (p - 1) ^ (h - 1)) + p * (p - 1) ^ h := by ring
    exact (Nat.dvd_add_right h1).mp (by simpa [add_assoc] using hdiv)
  have hcop : ¬ p ∣ (p - 1) ^ h := by
    intro hd
    have hle : p ≤ p - 1 := Nat.le_of_dvd (by omega) (hp.dvd_of_dvd_pow hd)
    omega
  rw [sq] at hsum_dvd
  exact hcop ((mul_dvd_mul_iff_left hp.ne_zero).mp hsum_dvd)

/-- Main theorem: `x = 81` is the only prime-power term of A008848. -/
theorem main_H1 : OMA.R_oeis_a008848_R1.H1 := by
  intro x hx
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hx ⊢
  rcases hx with ⟨⟨hxpos, ⟨s, hs⟩, ⟨y, hy⟩⟩, hpp⟩
  obtain ⟨p, k, hp_nat, hkpos, rfl⟩ := hpp
  have hp : p.Prime := hp_nat.nat_prime
  -- Since p^k = s * s, k is even: k = 2 * j with j ≥ 1
  have hk_even : Even k := by
    have : Fact p.Prime := ⟨hp⟩
    have hs0 : s ≠ 0 := by intro h0; rw [h0, mul_zero] at hs; exact pow_ne_zero k hp.ne_zero hs
    have hval := congrArg (padicValNat p) hs
    rw [padicValNat.prime_pow, padicValNat.mul hs0 hs0] at hval
    exact ⟨padicValNat p s, by omega⟩
  obtain ⟨j, hj⟩ := hk_even
  have hjpos : 1 ≤ j := by omega
  have h2j : k = 2 * j := by omega
  subst h2j
  -- Compute σ(p^(2j)) = ∑ i ∈ range (2j + 1), p^i and multiply by (p - 1)
  have hsigma : sigma 1 (p ^ (2 * j)) = ∑ i ∈ Finset.range (2 * j + 1), p ^ i := by
    rw [sigma_one_apply_prime_pow hp]
  have hgeom_all : ∀ n, (p - 1) * (∑ i ∈ Finset.range n, p ^ i) + 1 = p ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, pow_succ]
      have hp1 : p = (p - 1) + 1 := by have := hp.two_le; omega
      calc (p - 1) * (∑ i ∈ Finset.range n, p ^ i) + (p - 1) * p ^ n + 1
          = ((p - 1) * (∑ i ∈ Finset.range n, p ^ i) + 1) + (p - 1) * p ^ n := by ring
        _ = p ^ n + (p - 1) * p ^ n := by rw [ih]
        _ = p ^ n * ((p - 1) + 1) := by ring
        _ = p ^ n * p := by rw [← hp1]
  have hgeom : (p - 1) * (∑ i ∈ Finset.range (2 * j + 1), p ^ i) + 1 = p ^ (2 * j + 1) :=
    hgeom_all (2 * j + 1)
  have hpell : p * (p ^ j) ^ 2 = (p - 1) * y ^ 2 + 1 := by
    have hy2 : sigma 1 (p ^ (2 * j)) = y ^ 2 := by rw [hy, sq]
    rw [hsigma] at hy2
    rw [← hy2, ← pow_mul, mul_comm j 2, ← pow_succ']
    exact hgeom.symm
  -- Rule out p = 2 modulo 4
  have hp3 : 3 ≤ p := by
    by_contra! hlt
    have hp2 : p = 2 := by have := hp.two_le; omega
    subst hp2
    have h2 : 2 * (2 ^ j) ^ 2 = y ^ 2 + 1 := by simpa using hpell
    have h4 : 4 ∣ 2 * (2 ^ j) ^ 2 := by
      have : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
      obtain ⟨t, ht⟩ := this
      rw [ht]; exact ⟨2 * t ^ 2, by ring⟩
    have hmod : y ^ 2 % 4 = 3 := by omega
    have hsq4 : y ^ 2 % 4 = 0 ∨ y ^ 2 % 4 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one y with h0 | h1
      · left; have : y = 2 * (y / 2) := by omega
        rw [this]; ring_nf; omega
      · right; have : y = 2 * (y / 2) + 1 := by omega
        rw [this]; ring_nf; omega
    omega
  -- Apply Pell parametrization
  have hypos : 0 < y := by
    by_contra! hy0
    have hyz : y = 0 := by omega
    rw [hyz] at hpell
    have : 2 ≤ p * (p ^ j) ^ 2 := by nlinarith [Nat.one_le_pow j p hp.pos]
    omega
  obtain ⟨h, hu_eq, _⟩ := pell_param hp3 (p ^ j) y (pow_pos hp.pos j) hypos hpell
  rw [(recUV_eq_oddUV hp h).1] at hu_eq
  -- p ∣ p^j = oddU p 1 1 h, so p ∣ (2h + 1)
  have hp_dvd_m : p ∣ 2 * h + 1 := by
    rw [← prime_dvd_oddU_iff hp h, ← hu_eq]
    exact dvd_pow_self p (by omega)
  -- Case 1: p ≥ 5 is impossible
  by_cases hp5 : 5 ≤ p
  · have hodd_p : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
    obtain ⟨q, hq⟩ := hp_dvd_m
    have hq_odd : q % 2 = 1 := by
      by_contra hq0
      have : 2 ∣ q := by omega
      have : 2 ∣ 2 * h + 1 := by rw [hq]; exact dvd_mul_of_dvd_right this p
      omega
    set h₁ := (p - 1) / 2
    set h₂ := (q - 1) / 2
    have hm_eq : h = 2 * h₁ * h₂ + h₁ + h₂ := by
      have : 2 * h₁ + 1 = p := by omega
      have : 2 * h₂ + 1 = q := by omega
      nlinarith
    have hdvd_Up : oddU p 1 1 h₁ ∣ p ^ j := by
      rw [hu_eq, hm_eq]
      exact oddU_dvd_of_dvd hp
    obtain ⟨a, _, ha_eq⟩ := (Nat.dvd_prime_pow hp).mp hdvd_Up
    have ha_le1 : a ≤ 1 := by
      by_contra! ha2
      have hp2_dvd : p ^ 2 ∣ oddU p 1 1 h₁ := by
        rw [ha_eq]; exact Nat.pow_dvd_pow p ha2
      exact not_prime_sq_dvd_oddU_p hp hp5 hp2_dvd
    have hUp_le_p : oddU p 1 1 h₁ ≤ p := by
      rw [ha_eq]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha_le1 with rfl | rfl
      · simp; omega
      · simp
    have hUp_gt_p : p < oddU p 1 1 h₁ := by
      have hge := oddU_ge_first_term p h₁
      have h2h1 : 2 * h₁ + 1 = p := by omega
      rw [h2h1] at hge
      have hh1_ne : h₁ ≠ 0 := by dsimp [h₁]; omega
      have hpow : 1 < (p - 1) ^ h₁ := one_lt_pow₀ (by omega : 1 < p - 1) hh1_ne
      nlinarith only [hge, hpow, hp5]
    omega
  -- Case 2: p = 3
  · have hp4 : p ≠ 4 := fun h4 => by subst h4; exact absurd hp (by decide)
    have hp_eq3 : p = 3 := by omega
    subst hp_eq3
    -- First rule out 9 ∣ (2h + 1) using oddU 3 1 1 4 = 8721 = 17 * 513
    have hnot9 : ¬ 9 ∣ 2 * h + 1 := by
      intro h9
      obtain ⟨q, hq⟩ := h9
      have hq_odd : q % 2 = 1 := by
        by_contra hq0
        have : 2 ∣ q := by omega
        have : 2 ∣ 2 * h + 1 := by rw [hq]; exact dvd_mul_of_dvd_right this 9
        omega
      set h₂ := (q - 1) / 2
      have hm_eq : h = 2 * 4 * h₂ + 4 + h₂ := by omega
      have hdvd9 : oddU 3 1 1 4 ∣ 3 ^ j := by
        rw [hu_eq, hm_eq]; exact oddU_dvd_of_dvd (by decide)
      have hU9 : oddU 3 1 1 4 = 8721 := by
        rw [← (recUV_eq_oddUV (by decide : Nat.Prime 3) 4).1]; rfl
      rw [hU9] at hdvd9
      have h17 : 17 ∣ 3 ^ j := dvd_trans ⟨513, by norm_num⟩ hdvd9
      have h17_3 : 17 ∣ 3 := (by decide : Nat.Prime 17).dvd_of_dvd_pow h17
      omega
    -- Write 2h + 1 = 3 * s with s odd and ¬ 3 ∣ s
    obtain ⟨s, hs_eq⟩ := hp_dvd_m
    have hs_odd : s % 2 = 1 := by
      by_contra hs0
      have : 2 ∣ s := by omega
      have : 2 ∣ 2 * h + 1 := by rw [hs_eq]; exact dvd_mul_of_dvd_right this 3
      omega
    have hnot3s : ¬ 3 ∣ s := by
      intro h3s
      obtain ⟨t, ht⟩ := h3s
      exact hnot9 ⟨t, by linarith⟩
    set h₂ := (s - 1) / 2
    have hm_eq : h = 2 * h₂ * 1 + h₂ + 1 := by omega
    have hdvd_Us : oddU 3 1 1 h₂ ∣ 3 ^ j := by
      rw [hu_eq, hm_eq]
      exact oddU_dvd_of_dvd (by decide)
    have hnot3_Us : ¬ 3 ∣ oddU 3 1 1 h₂ := by
      rw [prime_dvd_oddU_iff (by decide)]
      have : 2 * h₂ + 1 = s := by omega
      rwa [this]
    obtain ⟨a, _, ha_eq⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hdvd_Us
    have ha0 : a = 0 := by
      by_contra ha_ne
      exact hnot3_Us (by rw [ha_eq]; exact dvd_pow_self 3 ha_ne)
    have hUs1 : oddU 3 1 1 h₂ = 1 := by rw [ha_eq, ha0]; simp
    have hh2_0 : h₂ = 0 := by
      have hge := oddU_ge_first_term 3 h₂
      rw [hUs1] at hge
      have hpow : 1 ≤ (3 - 1) ^ h₂ := Nat.one_le_pow h₂ 2 (by omega)
      nlinarith only [hge, hpow]
    have hh1 : h = 1 := by omega
    have hU3 : oddU 3 1 1 1 = 9 := by
      rw [← (recUV_eq_oddUV (by decide : Nat.Prime 3) 1).1]; rfl
    rw [hh1, hU3] at hu_eq
    have hj2 : j = 2 := by
      have : 3 ^ j = 3 ^ 2 := by omega
      exact Nat.pow_right_injective (by omega) this
    rw [hj2]
    norm_num

end OMA.OeisA008848H1

theorem OMA.solution : OMA.R_oeis_a008848_R1.H1 :=
  OMA.OeisA008848H1.main_H1
