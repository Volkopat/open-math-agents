import OMAStatements.S_oeis_a188571

-- Problem: OEIS A188571, Kimberling's conjecture (every prime divides a(n) for infinitely
-- many n) and Barker's recurrence a(n) = 4a(n-1) + 4a(n-2) - 16a(n-3) + 8a(n-4)
-- Statement: statements/oeis-a188571.lean (declaration OMA.S_oeis_a188571.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. The multiplication by alpha = 1 + sqrt(2) + sqrt(3) is a linear map F on Z^4, and
-- alpha is a root of x^4 = 4x^3 + 4x^2 - 16x + 8, which gives the recurrence. Thus a(n) is
-- even for n >= 4. Let p be an odd prime. The multiplication by -4 - 2 sqrt(2) + 2 sqrt(6) is
-- a map G with G(F(v)) = -8 v, so F is injective modulo p. The states modulo p are in a finite
-- set, so two of them are equal, and injectivity gives a period T >= 1 with state(kT) =
-- state(0) modulo p for all k. Since a(0) = 0, the prime p divides a(kT).

namespace OMA.A188571

open OMA.S_oeis_a188571

/-- Multiplication by `1 + √2 + √3` over a commutative ring. -/
def stepR {R : Type} [CommRing R] (v : R × R × R × R) : R × R × R × R :=
  (v.1 + 2 * v.2.1 + 3 * v.2.2.1, v.1 + v.2.1 + 3 * v.2.2.2, v.1 + v.2.2.1 + 2 * v.2.2.2,
    v.2.1 + v.2.2.1 + v.2.2.2)

/-- Multiplication by `-4 - 2√2 + 2√6`, which is `-8 / (1 + √2 + √3)`. -/
def backR {R : Type} [CommRing R] (v : R × R × R × R) : R × R × R × R :=
  (-4 * v.1 - 4 * v.2.1 + 12 * v.2.2.2, -2 * v.1 - 4 * v.2.1 + 6 * v.2.2.1,
    4 * v.2.1 - 4 * v.2.2.1 - 4 * v.2.2.2, 2 * v.1 - 2 * v.2.2.1 - 4 * v.2.2.2)

lemma back_step {R : Type} [CommRing R] (v : R × R × R × R) :
    backR (stepR v) = (-8 * v.1, -8 * v.2.1, -8 * v.2.2.1, -8 * v.2.2.2) := by
  simp only [backR, stepR]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> ring

/-- The coordinates modulo `p`. -/
def cast (p : ℕ) (v : ℤ × ℤ × ℤ × ℤ) : ZMod p × ZMod p × ZMod p × ZMod p :=
  ((v.1 : ZMod p), (v.2.1 : ZMod p), (v.2.2.1 : ZMod p), (v.2.2.2 : ZMod p))

lemma cast_step (p : ℕ) (v : ℤ × ℤ × ℤ × ℤ) : cast p (quadStep v) = stepR (cast p v) := by
  simp only [cast, quadStep, stepR]
  push_cast
  rfl

lemma step_injective (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Injective (stepR : ZMod p × ZMod p × ZMod p × ZMod p → _) := by
  have : Fact p.Prime := ⟨hp⟩
  have h8 : (-8 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((8 : ℕ) : ZMod p) = 0 := by
      have : (8 : ZMod p) = 0 := by linear_combination (-1 : ZMod p) * h
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h'
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using h')
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  intro v w hvw
  have h := congrArg backR hvw
  rw [back_step, back_step] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact Prod.ext (mul_left_cancel₀ h8 h1) (Prod.ext (mul_left_cancel₀ h8 h2)
    (Prod.ext (mul_left_cancel₀ h8 h3) (mul_left_cancel₀ h8 h4)))

/-- For an odd prime `p` the states modulo `p` are purely periodic. -/
lemma period (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ T : ℕ, 0 < T ∧ ∀ k : ℕ, cast p (quadPow (k * T)) = cast p (quadPow 0) := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj := step_injective p hp hp2
  have hsucc : ∀ n, cast p (quadPow (n + 1)) = stepR (cast p (quadPow n)) := fun n =>
    cast_step p (quadPow n)
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => cast p (quadPow n))
  -- we may assume `i < j`
  have key : ∀ i j : ℕ, i < j → cast p (quadPow i) = cast p (quadPow j) →
      cast p (quadPow 0) = cast p (quadPow (j - i)) := by
    intro i
    induction i with
    | zero =>
      intro j _ h
      simpa using h
    | succ i ih =>
      intro j hj h
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hsucc, hsucc] at h
      have h' := hinj h
      have := ih j' (by omega) h'
      rwa [show j' + 1 - (i + 1) = j' - i by omega]
  have hT : ∃ T : ℕ, 0 < T ∧ cast p (quadPow 0) = cast p (quadPow T) := by
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact ⟨j - i, by omega, key i j h heq⟩
    · exact ⟨i - j, by omega, key j i h heq.symm⟩
  obtain ⟨T, hTpos, hT0⟩ := hT
  have hshift : ∀ n, cast p (quadPow (n + T)) = cast p (quadPow n) := by
    intro n
    induction n with
    | zero =>
      rw [Nat.zero_add]
      exact hT0.symm
    | succ n ih =>
      rw [show n + 1 + T = (n + T) + 1 by ring, hsucc, hsucc, ih]
  refine ⟨T, hTpos, ?_⟩
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * T = k * T + T by ring, hshift, ih]

lemma rec4 (v : ℤ × ℤ × ℤ × ℤ) :
    (quadStep (quadStep (quadStep (quadStep v)))).2.1
      = 4 * (quadStep (quadStep (quadStep v))).2.1 + 4 * (quadStep (quadStep v)).2.1
        - 16 * (quadStep v).2.1 + 8 * v.2.1 := by
  simp only [quadStep]
  ring

lemma a_rec (m : ℕ) : a (m + 4) = 4 * a (m + 3) + 4 * a (m + 2) - 16 * a (m + 1) + 8 * a m := by
  exact rec4 (quadPow m)

theorem result :
    (∀ p : ℕ, Nat.Prime p → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (p : ℤ) ∣ a n) ∧
    ∀ n : ℕ, 4 ≤ n → a n = 4 * a (n - 1) + 4 * a (n - 2) - 16 * a (n - 3) + 8 * a (n - 4) := by
  constructor
  · intro p hp N
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨N + 4, by omega, ?_⟩
      rw [a_rec N]
      exact ⟨2 * a (N + 3) + 2 * a (N + 2) - 8 * a (N + 1) + 4 * a N, by push_cast; ring⟩
    · obtain ⟨T, hTpos, hT⟩ := period p hp hp2
      refine ⟨N * T, Nat.le_mul_of_pos_right N hTpos, ?_⟩
      have h := congrArg (fun v => v.2.1) (hT N)
      simp only [cast, quadPow] at h
      have h0 : ((a (N * T) : ℤ) : ZMod p) = 0 := by
        simpa [a] using h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show 4 + m = m + 4 by ring, show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
    exact a_rec m

end OMA.A188571

theorem OMA.solution : type_of% @OMA.S_oeis_a188571.main :=
  OMA.A188571.result
