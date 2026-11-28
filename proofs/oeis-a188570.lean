import OMAStatements.S_oeis_a188570

-- Problem: A188570, Kimberling's conjecture that every prime divides infinitely many a(n).
-- Credit: @ShoQo
-- Disproof: 23 divides no a(n). Mod 23 the coefficient vectors run through a cycle of length 22
-- starting at (1, 0, 0, 0) (checked: the 22nd iterate is (1, 0, 0, 0) again), and none of the
-- 22 vectors of the cycle has first coordinate 0 (checked by the kernel). So {n | 23 ∣ a(n)} is
-- empty, not infinite.

open OMA.S_oeis_a188570

namespace OMA_A188570_Disproof

def stepR (x : ZMod 23 × ZMod 23 × ZMod 23 × ZMod 23) : ZMod 23 × ZMod 23 × ZMod 23 × ZMod 23 :=
  (x.1 + 2 * x.2.1 + 3 * x.2.2.1, x.1 + x.2.1 + 3 * x.2.2.2, x.1 + x.2.2.1 + 2 * x.2.2.2,
    x.2.1 + x.2.2.1 + x.2.2.2)

/-- Reduction of a coefficient vector mod 23. -/
def red (x : ℤ × ℤ × ℤ × ℤ) : ZMod 23 × ZMod 23 × ZMod 23 × ZMod 23 :=
  ((x.1 : ZMod 23), (x.2.1 : ZMod 23), (x.2.2.1 : ZMod 23), (x.2.2.2 : ZMod 23))

lemma red_step (x : ℤ × ℤ × ℤ × ℤ) : red (step x) = stepR (red x) := by
  simp [red, step, stepR]

def v (n : ℕ) : ZMod 23 × ZMod 23 × ZMod 23 × ZMod 23 := stepR^[n] (1, 0, 0, 0)

lemma red_coeffs (n : ℕ) : red (coeffs n) = v n := by
  induction n with
  | zero => simp [red, coeffs, v]
  | succ n ih =>
    rw [coeffs, Function.iterate_succ_apply', ← coeffs, red_step, ih, v, v,
      Function.iterate_succ_apply']

lemma dvd_iff (n : ℕ) : ((23 : ℕ) : ℤ) ∣ a n ↔ (v n).1 = 0 := by
  rw [← red_coeffs, red, ZMod.intCast_zmod_eq_zero_iff_dvd]; rfl

lemma v_add (n k : ℕ) : v (n + k) = stepR^[k] (v n) := by
  rw [v, v, add_comm, Function.iterate_add_apply]

lemma v_22 : v 22 = v 0 := by decide +kernel

lemma v_small : ∀ n < 22, (v n).1 ≠ 0 := by decide +kernel

lemma v_periodic (n : ℕ) : v (n + 22) = v n := by
  rw [add_comm, v_add, v_22, ← v_add, zero_add]

lemma v_ne (n : ℕ) : (v n).1 ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 22 with h | h
    · exact v_small n h
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 22 := ⟨n - 22, by omega⟩
      rw [v_periodic]; exact ih m (by omega)

end OMA_A188570_Disproof

open OMA_A188570_Disproof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a188570.main) := by
  intro h
  obtain ⟨hinf, -⟩ := h 23 (by norm_num)
  apply hinf
  have : {n : ℕ | ((23 : ℕ) : ℤ) ∣ a n} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, dvd_iff]
    exact v_ne n
  rw [this]; exact Set.finite_empty
