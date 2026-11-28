import OMAStatements.S_oeis_a041243
import Mathlib

/-!
# oeis-a041243: the continued fraction recurrence for the denominators of the convergents to sqrt 133

The integer algorithm for the continued fraction of a square root tracks the complete quotients
as (sqrt D + m) / d. Its states are periodic (period 16), and a decidable check shows that each
step agrees with the real computation in Mathlib (floor and inverse of the fractional part).
So the partial quotients are periodic, and the convergents satisfy the three-term recurrence
with these coefficients. Its shift u(n) = x(n + 2L) - 5177198 x(n + L) + x(n) solves the
same recurrence, and the kernel checks u(0) = u(1) = 0 through integer coefficients.

Source: OEIS A041243, https://oeis.org/A041243.
-/
namespace OMA.P_oeis_a041243

open GenContFract

/-- One step of the integer algorithm for the continued fraction of `sqrt 133`:
the complete quotient `(sqrt 133 + m) / d` goes to `(sqrt 133 + m') / d'`. -/
def nxt (x : ℤ × ℤ) : ℤ × ℤ :=
  ((x.1 + 11) / x.2 * x.2 - x.1, (133 - ((x.1 + 11) / x.2 * x.2 - x.1) ^ 2) / x.2)

/-- The states `(m, d)` of the algorithm. -/
def st : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | n + 1 => nxt (st n)

/-- The partial quotients. -/
def pq (n : ℕ) : ℤ := ((st n).1 + 11) / (st n).2

/-- The state conditions that make one step of the algorithm agree with the real computation. -/
def Good (x : ℤ × ℤ) : Prop :=
  0 < x.2 ∧ 0 < (nxt x).2 ∧ (x.1 + 11) / x.2 * x.2 - x.1 ≤ 11 ∧
    12 ≤ ((x.1 + 11) / x.2 + 1) * x.2 - x.1 ∧
    x.2 * (nxt x).2 = 133 - (nxt x).1 ^ 2

instance (x : ℤ × ℤ) : Decidable (Good x) := by unfold Good; infer_instance

theorem st_period (n : ℕ) : st (n + 17) = st (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih => show nxt (st (n + 17)) = nxt (st (n + 1)); rw [ih]

theorem good_st (n : ℕ) : Good (st n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 17 with h | h
    · interval_cases n <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 17 := ⟨n - 17, by omega⟩
      rw [st_period]; exact ih _ (by omega)

theorem pq_period (n : ℕ) : pq (n + 17) = pq (n + 1) := by
  simp only [pq, st_period]

lemma sqrt_lo : (11 : ℝ) < Real.sqrt 133 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma sqrt_hi : Real.sqrt 133 < 12 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma sqrt_sq : Real.sqrt 133 ^ 2 = 133 := Real.sq_sqrt (by norm_num)

/-- The real step, given the integer conditions. -/
lemma real_step (x : ℤ × ℤ) (h : Good x) :
    ⌊(Real.sqrt 133 + x.1) / x.2⌋ = (x.1 + 11) / x.2 ∧
    Int.fract ((Real.sqrt 133 + x.1) / x.2) ≠ 0 ∧
    (Int.fract ((Real.sqrt 133 + x.1) / x.2))⁻¹ =
      (Real.sqrt 133 + (nxt x).1) / (nxt x).2 := by
  obtain ⟨hQ, hQ', h1, h2, h3⟩ := h
  set q := (x.1 + 11) / x.2 with hq
  have hm : (nxt x).1 = q * x.2 - x.1 := rfl
  set m' := (nxt x).1
  set Q' := (nxt x).2
  have hQr : (0 : ℝ) < x.2 := by exact_mod_cast hQ
  have hQr' : (0 : ℝ) < Q' := by exact_mod_cast hQ'
  have h1r : ((q * x.2 - x.1 : ℤ) : ℝ) ≤ 11 := by exact_mod_cast h1
  have h2r : (12 : ℝ) ≤ (((q + 1) * x.2 - x.1 : ℤ) : ℝ) := by exact_mod_cast h2
  push_cast at h1r h2r
  have hfl : ⌊(Real.sqrt 133 + x.1) / x.2⌋ = q := by
    rw [Int.floor_eq_iff, le_div_iff₀ hQr, div_lt_iff₀ hQr]
    constructor <;> nlinarith [sqrt_lo, sqrt_hi]
  have hfr : Int.fract ((Real.sqrt 133 + x.1) / x.2) = (Real.sqrt 133 - m') / x.2 := by
    rw [Int.fract, hfl, hm]; push_cast; field_simp; ring
  have hne : Real.sqrt 133 - m' ≠ 0 := by
    have : ((x.2 * Q' : ℤ) : ℝ) = 133 - (m' : ℝ) ^ 2 := by rw [h3]; push_cast; ring
    push_cast at this
    intro h0
    have : (m' : ℝ) = Real.sqrt 133 := by linarith
    have hm1 : (m' : ℝ) ≤ 11 := by rw [hm]; push_cast; linarith
    linarith [sqrt_lo]
  refine ⟨hfl, ?_, ?_⟩
  · rw [hfr]; exact div_ne_zero hne hQr.ne'
  · rw [hfr, inv_div]
    have h3r : ((x.2 * Q' : ℤ) : ℝ) = 133 - (m' : ℝ) ^ 2 := by rw [h3]; push_cast; ring
    push_cast at h3r
    rw [div_eq_div_iff hne hQr'.ne']
    nlinarith [sqrt_sq]

lemma stream_eq (n : ℕ) : IntFractPair.stream (Real.sqrt 133) n =
    some (IntFractPair.of ((Real.sqrt 133 + (st n).1) / (st n).2)) := by
  induction n with
  | zero =>
    rw [IntFractPair.stream_zero]; simp [st]
  | succ n ih =>
    obtain ⟨-, hfr, hinv⟩ := real_step (st n) (good_st n)
    rw [IntFractPair.stream_succ_of_some ih (by simpa [IntFractPair.of] using hfr)]
    simp only [IntFractPair.of] at hinv ⊢
    rw [hinv]; rfl

lemma s_get (n : ℕ) : (GenContFract.of (Real.sqrt 133)).s.get? n =
    some ⟨1, (pq (n + 1) : ℝ)⟩ := by
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream (stream_eq (n + 1))]
  obtain ⟨hfl, -, -⟩ := real_step (st (n + 1)) (good_st (n + 1))
  simp only [IntFractPair.of, hfl, pq]

/-- Integer coefficients expressing a solution of the recurrence via its first two terms:
`cf n = ((α n, β n), (α (n+1), β (n+1)))` with `x n = α n * x 0 + β n * x 1`. -/
def cf : ℕ → (ℤ × ℤ) × (ℤ × ℤ)
  | 0 => ((1, 0), (0, 1))
  | n + 1 => ((cf n).2, (pq (n + 2) * (cf n).2.1 + (cf n).1.1, pq (n + 2) * (cf n).2.2 + (cf n).1.2))

theorem rec (n : ℕ) : OMA.S_oeis_a041243.a (n + 2) =
    (pq (n + 2) : ℝ) * OMA.S_oeis_a041243.a (n + 1) + OMA.S_oeis_a041243.a n := by
  have := dens_recurrence (g := GenContFract.of (Real.sqrt 133)) (s_get (n + 1)) rfl rfl
  simpa [OMA.S_oeis_a041243.a] using this

theorem closed (n : ℕ) :
    OMA.S_oeis_a041243.a n = (cf n).1.1 * OMA.S_oeis_a041243.a 0 +
        (cf n).1.2 * OMA.S_oeis_a041243.a 1 ∧
    OMA.S_oeis_a041243.a (n + 1) = (cf n).2.1 * OMA.S_oeis_a041243.a 0 +
        (cf n).2.2 * OMA.S_oeis_a041243.a 1 := by
  induction n with
  | zero => simp [cf]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [rec, ih.1, ih.2]
    simp only [cf]; push_cast; ring

theorem main : ∀ n : ℕ, OMA.S_oeis_a041243.a (n + 32) =
    5177198 * OMA.S_oeis_a041243.a (n + 16) - OMA.S_oeis_a041243.a n := by
  let u : ℕ → ℝ := fun n => OMA.S_oeis_a041243.a (n + 32) -
    5177198 * OMA.S_oeis_a041243.a (n + 16) + OMA.S_oeis_a041243.a n
  have hu : ∀ n, u (n + 2) = (pq (n + 2) : ℝ) * u (n + 1) + u n := by
    intro n
    have e1 := rec n
    have e2 := rec (n + 16)
    have e3 := rec (n + 32)
    have q1 : pq (n + 16 + 2) = pq (n + 2) := by
      rw [show n + 16 + 2 = (n + 1) + 17 by omega, pq_period]
    have q2 : pq (n + 32 + 2) = pq (n + 2) := by
      rw [show n + 32 + 2 = (n + 17) + 17 by omega, pq_period,
        show n + 17 + 1 = (n + 1) + 17 by omega, pq_period]
    rw [q1] at e2; rw [q2] at e3
    simp only [u, show n + 2 + 32 = n + 32 + 2 by omega, show n + 2 + 16 = n + 16 + 2 by omega,
      show n + 1 + 32 = n + 32 + 1 by omega, show n + 1 + 16 = n + 16 + 1 by omega]
    rw [e1, e2, e3]; ring
  have c0 : (cf 32).1.1 - 5177198 * (cf 16).1.1 + 1 = 0 ∧
      (cf 32).1.2 - 5177198 * (cf 16).1.2 = 0 ∧
      (cf 32).2.1 - 5177198 * (cf 16).2.1 = 0 ∧
      (cf 32).2.2 - 5177198 * (cf 16).2.2 + 1 = 0 := by
    set_option maxRecDepth 100000 in decide
  obtain ⟨hA, hB, hA1, hB1⟩ := c0
  have hA' : (((cf 32).1.1 - 5177198 * (cf 16).1.1 + 1 : ℤ) : ℝ) = 0 := by rw [hA]; simp
  have hB' : (((cf 32).1.2 - 5177198 * (cf 16).1.2 : ℤ) : ℝ) = 0 := by rw [hB]; simp
  have hA1' : (((cf 32).2.1 - 5177198 * (cf 16).2.1 : ℤ) : ℝ) = 0 := by rw [hA1]; simp
  have hB1' : (((cf 32).2.2 - 5177198 * (cf 16).2.2 + 1 : ℤ) : ℝ) = 0 := by rw [hB1]; simp
  push_cast at hA' hB' hA1' hB1'
  have u0 : u 0 = 0 := by
    simp only [u]; rw [(closed 32).1, (closed 16).1]
    linear_combination OMA.S_oeis_a041243.a 0 * hA' + OMA.S_oeis_a041243.a 1 * hB'
  have u1 : u 1 = 0 := by
    simp only [u]; rw [(closed 32).2, (closed 16).2]
    linear_combination OMA.S_oeis_a041243.a 0 * hA1' + OMA.S_oeis_a041243.a 1 * hB1'
  have hz : ∀ n, u n = 0 ∧ u (n + 1) = 0 := by
    intro n
    induction n with
    | zero => exact ⟨u0, u1⟩
    | succ n ih => exact ⟨ih.2, by rw [hu, ih.1, ih.2]; ring⟩
  intro n
  have := (hz n).1
  simp only [u] at this
  linarith

end OMA.P_oeis_a041243

theorem OMA.solution : type_of% @OMA.S_oeis_a041243.main := OMA.P_oeis_a041243.main

