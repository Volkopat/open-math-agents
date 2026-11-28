import OMAStatements.S_oeis_a188573

-- Problem: A188573, Kimberling's conjecture: every prime p divides infinitely many a(n), and
-- the indices form an eventually periodic set.
-- Credit: @ShoQo
-- Proof: reduce the coefficient vectors mod p. They are the orbit of (1,0,0,0) under the map
-- `step` on the finite set (ZMod p)^4, hence eventually periodic (pigeonhole), which is the
-- second part. For p = 2 every coordinate is even from n = 2 on. For odd p, `step` is
-- invertible mod p: its adjugate G satisfies G (step x) = -8 x. So the orbit is purely
-- periodic, returns to (1,0,0,0), whose last coordinate is 0, at every multiple of the period.

open OMA.S_oeis_a188573

namespace OMA_A188573_Proof

variable {R : Type*} [CommRing R]

def stepR (x : R × R × R × R) : R × R × R × R :=
  (x.1 + 2 * x.2.1 + 3 * x.2.2.1, x.1 + x.2.1 + 3 * x.2.2.2, x.1 + x.2.2.1 + 2 * x.2.2.2,
    x.2.1 + x.2.2.1 + x.2.2.2)

/-- The adjugate of `step`. -/
def adjR (x : R × R × R × R) : R × R × R × R :=
  (-4 * x.1 - 4 * x.2.1 + 12 * x.2.2.2, -2 * x.1 - 4 * x.2.1 + 6 * x.2.2.1,
    4 * x.2.1 - 4 * x.2.2.1 - 4 * x.2.2.2, 2 * x.1 - 2 * x.2.2.1 - 4 * x.2.2.2)

lemma adj_step (x : R × R × R × R) : adjR (stepR x) = (-8 : R) • x := by
  obtain ⟨a, b, c, d⟩ := x
  simp only [adjR, stepR, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- Reduction of a coefficient vector mod p. -/
def red (p : ℕ) (x : ℤ × ℤ × ℤ × ℤ) : ZMod p × ZMod p × ZMod p × ZMod p :=
  ((x.1 : ZMod p), (x.2.1 : ZMod p), (x.2.2.1 : ZMod p), (x.2.2.2 : ZMod p))

lemma red_step (p : ℕ) (x : ℤ × ℤ × ℤ × ℤ) : red p (step x) = stepR (red p x) := by
  simp [red, step, stepR]

/-- The reduced orbit. -/
def v (p : ℕ) (n : ℕ) : ZMod p × ZMod p × ZMod p × ZMod p := (stepR)^[n] (1, 0, 0, 0)

lemma red_coeffs (p n : ℕ) : red p (coeffs n) = v p n := by
  induction n with
  | zero => simp [red, coeffs, v]
  | succ n ih =>
    rw [coeffs, Function.iterate_succ_apply', ← coeffs, red_step, ih, v, v,
      Function.iterate_succ_apply']

lemma dvd_iff (p n : ℕ) : (p : ℤ) ∣ a n ↔ (v p n).2.2.2 = 0 := by
  rw [← red_coeffs, red, ZMod.intCast_zmod_eq_zero_iff_dvd]; rfl

lemma v_succ (p n : ℕ) : v p (n + 1) = stepR (v p n) := by
  rw [v, v, Function.iterate_succ_apply']

lemma v_add (p n k : ℕ) : v p (n + k) = (stepR)^[k] (v p n) := by
  rw [v, v, add_comm, Function.iterate_add_apply]

/-- Pigeonhole: the reduced orbit is eventually periodic. -/
lemma eventually_periodic (p : ℕ) [NeZero p] :
    ∃ N T, 0 < T ∧ ∀ n, N ≤ n → v p (n + T) = v p n := by
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (v p)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨i, j - i, by omega, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = i + k := ⟨n - i, by omega⟩
    rw [show i + k + (j - i) = j + k by omega, v_add, v_add, h]
  · refine ⟨j, i - j, by omega, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
    rw [show j + k + (i - j) = i + k by omega, v_add, v_add, h]

lemma stepR_injective {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Function.Injective (stepR : ZMod p × ZMod p × ZMod p × ZMod p → _) := by
  have h8 : (-8 : ZMod p) ≠ 0 := by
    rw [neg_ne_zero, show (8 : ZMod p) = ((2 ^ 3 : ℕ) : ZMod p) by norm_num, Ne,
      ZMod.natCast_eq_zero_iff]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1
      ((Fact.out : p.Prime).dvd_of_dvd_pow h))
  intro x y hxy
  have := congrArg adjR hxy
  rw [adj_step, adj_step] at this
  exact smul_right_injective _ h8 this

end OMA_A188573_Proof

open OMA_A188573_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a188573.main := by
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨N, T, hT, hper⟩ := eventually_periodic p
  refine ⟨?_, N, T, hT, fun n hn => by rw [dvd_iff, dvd_iff, hper n hn]⟩
  by_cases hp2 : p = 2
  · -- every a(n) with n ≥ 2 is even
    subst hp2
    have hv2 : v 2 2 = 0 := by decide +revert
    have h0 : ∀ k, v 2 (2 + k) = 0 := by
      intro k
      induction k with
      | zero => exact hv2
      | succ k ih =>
        rw [← add_assoc, v_succ, ih]
        simp [stepR, Prod.ext_iff]
    apply Set.infinite_of_not_bddAbove
    rintro ⟨m, hm⟩
    have : 2 + m ∈ {n : ℕ | ((2 : ℕ) : ℤ) ∣ a n} := by
      simp only [Set.mem_ofPred_eq, dvd_iff, h0]; rfl
    have := hm this
    omega
  · -- odd p: the orbit is purely periodic, so it returns to (1, 0, 0, 0)
    have hinj := stepR_injective (p := p) hp2
    have hback : ∀ m, v p (m + T) = v p m := by
      intro m
      induction' h : N - m with k ih generalizing m
      · exact hper m (by omega)
      · have := ih (m + 1) (by omega)
        rw [show m + 1 + T = (m + T) + 1 by omega, v_succ, v_succ] at this
        exact hinj this
    have hmul : ∀ k, v p (k * T) = v p 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.succ_mul, hback, ih]
    apply Set.infinite_of_not_bddAbove
    rintro ⟨m, hm⟩
    have hmem : (m + 1) * T ∈ {n : ℕ | (p : ℤ) ∣ a n} := by
      simp only [Set.mem_ofPred_eq, dvd_iff, hmul]; simp [v]
    have := hm hmem
    nlinarith
