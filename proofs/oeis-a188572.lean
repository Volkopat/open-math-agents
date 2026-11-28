import OMAStatements.S_oeis_a188572

/-! Modulo an odd prime, the update of the four coordinates is a permutation.
Modulo two, applying it twice gives zero. -/

namespace A188572Proof

open OMA.S_oeis_a188572

private abbrev Coords (p : ℕ) := ZMod p × ZMod p × ZMod p × ZMod p

private def step {p : ℕ} (v : Coords p) : Coords p :=
  let (a,b,c,d) := v
  (a + 2*b + 3*c, a + b + 3*d, a + c + 2*d, b + c + d)

private def undoScaled {p : ℕ} (v : Coords p) : Coords p :=
  let (a,b,c,d) := v
  (-4*a - 4*b + 12*d, -2*a - 4*b + 6*c, 4*b - 4*c - 4*d, 2*a - 2*c - 4*d)

private theorem undo_step {p : ℕ} (v : Coords p) : undoScaled (step v) =
    ((-8)*v.1, (-8)*v.2.1, (-8)*v.2.2.1, (-8)*v.2.2.2) := by
  rcases v with ⟨a,b,c,d⟩
  simp only [step, undoScaled, Prod.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

private def reduced (p n : ℕ) : Coords p :=
  let (a,b,c,d) := quadPow n
  ((a : ZMod p), (b : ZMod p), (c : ZMod p), (d : ZMod p))

private theorem reduced_succ (p n : ℕ) : reduced p (n+1) = step (reduced p n) := by
  rcases hx : quadPow n with ⟨a,b,c,d⟩
  simp [reduced, quadPow, hx, quadStep, step, Int.cast_add, Int.cast_mul]

private theorem to_dvd (p n : ℕ) (h : (reduced p n).2.2.1 = 0) : (p : ℤ) ∣ a n := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a n) p).mp
  rcases hx : quadPow n with ⟨a,b,c,d⟩
  simpa [reduced, OMA.S_oeis_a188572.a, hx] using h

private theorem two_steps_zero : ∀ v : Coords 2, step (step v) = (0,0,0,0) := by
  decide

private theorem step_injective {p : ℕ} [Fact p.Prime] (hn : (-8 : ZMod p) ≠ 0) :
    Function.Injective (step (p := p)) := by
  rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ h
  have h' := congrArg undoScaled h
  rw [undo_step, undo_step] at h'
  simp only [Prod.mk.injEq] at h' ⊢
  exact ⟨mul_left_cancel₀ hn h'.1, mul_left_cancel₀ hn h'.2.1,
    mul_left_cancel₀ hn h'.2.2.1, mul_left_cancel₀ hn h'.2.2.2⟩

theorem infinitely_often (p : ℕ) (hp : p.Prime) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ (p : ℤ) ∣ a n := by
  by_cases htwo : p = 2
  · subst p
    refine ⟨N+2, by omega, to_dvd 2 _ ?_⟩
    rw [show N+2 = (N+1)+1 by omega, reduced_succ, reduced_succ, two_steps_zero]
  · let _ : Fact p.Prime := ⟨hp⟩
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
      have hge := hp.two_le
      omega
    have h8 : (-8 : ZMod p) ≠ 0 := by
      rw [show (-8 : ZMod p) = -((2 : ZMod p)^3) by ring]
      exact neg_ne_zero.mpr (pow_ne_zero _ h2)
    have hi := step_injective h8
    let e : Equiv.Perm (Coords p) := Equiv.ofBijective step ⟨hi, Finite.injective_iff_surjective.mp hi⟩
    have hpow (n : ℕ) : reduced p n = (e^n) (1,0,0,0) := by
      induction n with
      | zero => simp [reduced, quadPow]
      | succ n ih => rw [reduced_succ, ih, pow_succ']; rfl
    refine ⟨orderOf e * (N+1), ?_, to_dvd p _ ?_⟩
    · exact (Nat.le_succ N).trans (Nat.le_mul_of_pos_left _ (orderOf_pos e))
    · rw [hpow, pow_mul, pow_orderOf_eq_one, one_pow]
      rfl

end A188572Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a188572.main := A188572Proof.infinitely_often
