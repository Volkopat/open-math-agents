import OMAStatements.S_oeis_a377112

namespace OMA.S_oeis_a377112




/-! ### The link with real numbers (a control on the definition) -/

theorem coeffs_real (n : ℕ) :
    (2 + Real.sqrt 2 + Real.sqrt 3) ^ n = (coeffs n).1 + (coeffs n).2.1 * Real.sqrt 2 +
      (coeffs n).2.2.1 * Real.sqrt 3 + (coeffs n).2.2.2 * Real.sqrt 6 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  induction n with
  | zero => simp [coeffs]
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [coeffs, step]
    push_cast
    rw [h6]
    linear_combination (((coeffs n).2.1 : ℝ) + ((coeffs n).2.2.2 : ℝ) * Real.sqrt 3) * h2 +
      (((coeffs n).2.2.1 : ℝ) + ((coeffs n).2.2.2 : ℝ) * Real.sqrt 2) * h3

theorem control_terms : (List.range 6).map a = [0, 0, 2, 12, 68, 360] := by decide

/-! ### Reduction modulo p -/

/-- The same linear map over `ZMod p`. -/
def stepZ (p : ℕ) (v : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p × ZMod p × ZMod p × ZMod p :=
  (2 * v.1 + 2 * v.2.1 + 3 * v.2.2.1,
   v.1 + 2 * v.2.1 + 3 * v.2.2.2,
   v.1 + 2 * v.2.2.1 + 2 * v.2.2.2,
   v.2.1 + v.2.2.1 + 2 * v.2.2.2)

/-- The coefficient vector reduced modulo p. -/
def w (p n : ℕ) : ZMod p × ZMod p × ZMod p × ZMod p :=
  (((coeffs n).1 : ℤ), ((coeffs n).2.1 : ℤ), ((coeffs n).2.2.1 : ℤ), ((coeffs n).2.2.2 : ℤ))

lemma w_succ (p n : ℕ) : w p (n + 1) = stepZ p (w p n) := by
  simp only [w, coeffs, step, stepZ]
  push_cast
  rfl

lemma w_zero (p : ℕ) : w p 0 = (1, 0, 0, 0) := by
  simp [w, coeffs]

lemma w_add (p n j : ℕ) : w p (n + j) = (stepZ p)^[j] (w p n) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, w_succ, ih, Function.iterate_succ_apply']

lemma dvd_iff (p n : ℕ) : (p : ℤ) ∣ a n ↔ (w p n).2.2.2 = 0 := by
  simp only [w, a]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm

/-- The adjugate of the step map: `adjZ (stepZ v) = -23 • v`. -/
def adjZ (p : ℕ) (v : ZMod p × ZMod p × ZMod p × ZMod p) : ZMod p × ZMod p × ZMod p × ZMod p :=
  (-2 * v.1 - 10 * v.2.1 - 9 * v.2.2.1 + 24 * v.2.2.2,
   -5 * v.1 - 2 * v.2.1 + 12 * v.2.2.1 - 9 * v.2.2.2,
   -3 * v.1 + 8 * v.2.1 - 2 * v.2.2.1 - 10 * v.2.2.2,
   4 * v.1 - 3 * v.2.1 - 5 * v.2.2.1 - 2 * v.2.2.2)

lemma adj_step (p : ℕ) (v : ZMod p × ZMod p × ZMod p × ZMod p) :
    adjZ p (stepZ p v) = ((-23) * v.1, (-23) * v.2.1, (-23) * v.2.2.1, (-23) * v.2.2.2) := by
  obtain ⟨x, y, z, t⟩ := v
  simp only [adjZ, stepZ, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring⟩

lemma stepZ_injective (p : ℕ) [hp : Fact p.Prime] (h23 : p ≠ 23) : Function.Injective (stepZ p) := by
  intro v v' h
  have h1 := adj_step p v
  have h2 := adj_step p v'
  rw [h] at h1
  rw [h1] at h2
  have hne : ((-23 : ZMod p)) ≠ 0 := by
    intro h0
    have : ((23 : ℕ) : ZMod p) = 0 := by
      have : (23 : ZMod p) = 0 := by
        have := congrArg Neg.neg h0
        simpa using this
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp this
    exact h23 this
  obtain ⟨x, y, z, t⟩ := v
  obtain ⟨x', y', z', t'⟩ := v'
  simp only [Prod.mk.injEq] at h2
  obtain ⟨e1, e2, e3, e4⟩ := h2
  simp only [Prod.mk.injEq]
  exact ⟨mul_left_cancel₀ hne e1, mul_left_cancel₀ hne e2,
    mul_left_cancel₀ hne e3, mul_left_cancel₀ hne e4⟩

/-- Eventual periodicity of the reduced vectors, for every p > 0. -/
lemma eventually_periodic (p : ℕ) [NeZero p] :
    ∃ m T : ℕ, 0 < T ∧ ∀ k, m ≤ k → w p (k + T) = w p k := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (w p)
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨i, j - i, by omega, fun k hk => ?_⟩
    have hk' : k = i + (k - i) := by omega
    have e1 : w p (k + (j - i)) = (stepZ p)^[k - i] (w p j) := by
      rw [← w_add]; congr 1; omega
    rw [e1, ← heq, ← w_add, ← hk']
  · refine ⟨j, i - j, by omega, fun k hk => ?_⟩
    have hk' : k = j + (k - j) := by omega
    have e1 : w p (k + (i - j)) = (stepZ p)^[k - j] (w p i) := by
      rw [← w_add]; congr 1; omega
    rw [e1, heq, ← w_add, ← hk']

lemma infinite_of_multiples (P : ℕ → Prop) (T : ℕ) (hT : 0 < T) (b : ℕ)
    (h : ∀ k, P (b + k * T)) : (Set.ofPred P).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k => b + k * T)
  · intro x y hxy
    simp only at hxy
    have := Nat.eq_of_mul_eq_mul_right hT (by omega : x * T = y * T)
    exact this
  · intro k
    exact h k

theorem rec23 : w 23 (16 + 22) = w 23 16 := by decide +kernel

theorem zero23 : (w 23 16).2.2.2 = 0 := by decide +kernel

theorem infinitely_many (p : ℕ) (hp : p.Prime) : {n : ℕ | (p : ℤ) ∣ a n}.Infinite := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases h23 : p = 23
  · subst h23
    have hrec := rec23
    have hzero := zero23
    have hall : ∀ k, w 23 (16 + k * 22) = w 23 16 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have : 16 + (k + 1) * 22 = (16 + 22) + k * 22 := by ring
        rw [this, w_add, hrec, ← w_add, ih]
    apply infinite_of_multiples _ 22 (by norm_num) 16
    intro k
    rw [dvd_iff, hall k, hzero]
  · obtain ⟨m, T, hT, hper⟩ := eventually_periodic p
    have hinj := (stepZ_injective p h23).iterate m
    have hT0 : w p T = w p 0 := by
      apply hinj
      rw [← w_add, ← w_add, Nat.add_comm 0 m, Nat.add_comm T m, Nat.add_zero]
      exact hper m le_rfl
    have hall : ∀ k, w p (0 + k * T) = w p 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have : 0 + (k + 1) * T = T + k * T := by ring
        rw [this, w_add, hT0, ← w_add, ih]
    apply infinite_of_multiples _ T hT 0
    intro k
    rw [dvd_iff, hall k, w_zero]

/-! ### Gaps of an eventually periodic infinite set -/

section Gaps

variable (P : ℕ → Prop) [DecidablePred P]

lemma count_window (n0 T : ℕ) (hper : ∀ k, n0 ≤ k → (P (k + T) ↔ P k)) :
    ∀ x, n0 ≤ x → Nat.count P (x + T) = Nat.count P x + (Nat.count P (n0 + T) - Nat.count P n0) := by
  have hmono : Nat.count P n0 ≤ Nat.count P (n0 + T) := Nat.count_monotone P (by omega)
  intro x hx
  induction x, hx using Nat.le_induction with
  | base => omega
  | succ x hx ih =>
    rw [show x + 1 + T = (x + T) + 1 by ring, Nat.count_succ, Nat.count_succ, ih]
    have := hper x hx
    by_cases hPx : P x
    · rw [if_pos (this.mpr hPx), if_pos hPx]; ring
    · rw [if_neg (fun h => hPx (this.mp h)), if_neg hPx]; ring

lemma gaps_periodic (hinf : (Set.ofPred P).Infinite) (n0 T : ℕ) (hT : 0 < T)
    (hper : ∀ k, n0 ≤ k → (P (k + T) ↔ P k)) :
    ∃ N0 Q : ℕ, 0 < Q ∧ ∀ i, N0 ≤ i →
      Nat.nth P (i + Q + 1) - Nat.nth P (i + Q) = Nat.nth P (i + 1) - Nat.nth P i := by
  set c := Nat.count P (n0 + T) - Nat.count P n0 with hc
  have hwin := count_window P n0 T hper
  have hinf' : (Set.ofPred P).Infinite := hinf
  -- c > 0: otherwise the count would be bounded
  have hcpos : 0 < c := by
    by_contra h0
    have h0' : c = 0 := by omega
    have hbound : ∀ j, Nat.count P (n0 + j * T) = Nat.count P n0 := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [show n0 + (j + 1) * T = (n0 + j * T) + T by ring, hwin _ (by omega), ih, ← hc, h0']
        rfl
    have hle : ∀ y, Nat.count P y ≤ Nat.count P n0 := by
      intro y
      calc Nat.count P y ≤ Nat.count P (n0 + y * T) :=
            Nat.count_monotone P (by nlinarith)
        _ = Nat.count P n0 := hbound y
    have := Nat.count_nth_of_infinite hinf' (Nat.count P n0 + 1)
    have := hle (Nat.nth P (Nat.count P n0 + 1))
    omega
  have hshift : ∀ i, n0 ≤ i → Nat.nth P (i + c) = Nat.nth P i + T := by
    intro i hi
    have hx := Nat.nth_mem_of_infinite hinf' i
    have hcnt := Nat.count_nth_of_infinite hinf' i
    have hge : n0 ≤ Nat.nth P i := le_trans hi ((Nat.nth_strictMono hinf').id_le i)
    have hPT : P (Nat.nth P i + T) := (hper _ hge).mpr hx
    have hcount : Nat.count P (Nat.nth P i + T) = i + c := by
      rw [hwin _ hge, hcnt]
    rw [← hcount, Nat.nth_count hPT]
  refine ⟨n0, c, hcpos, fun i hi => ?_⟩
  have e1 := hshift i hi
  have e2 := hshift (i + 1) (by omega)
  rw [show i + c + 1 = i + 1 + c by ring, e2, e1]
  omega

end Gaps

theorem gaps (p : ℕ) (hp : p.Prime) :
    ∃ N0 Q : ℕ, 0 < Q ∧ ∀ i, N0 ≤ i →
      Nat.nth (fun n => (p : ℤ) ∣ a n) (i + Q + 1) - Nat.nth (fun n => (p : ℤ) ∣ a n) (i + Q) =
      Nat.nth (fun n => (p : ℤ) ∣ a n) (i + 1) - Nat.nth (fun n => (p : ℤ) ∣ a n) i := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨m, T, hT, hper⟩ := eventually_periodic p
  apply gaps_periodic _ (infinitely_many p hp) m T hT
  intro k hk
  rw [dvd_iff, dvd_iff, hper k hk]

/-- Kimberling's conjecture, for every prime. -/
theorem conjecture : ∀ p : ℕ, p.Prime →
    {n : ℕ | (p : ℤ) ∣ a n}.Infinite ∧
    ∃ N0 Q : ℕ, 0 < Q ∧ ∀ i, N0 ≤ i →
      Nat.nth (fun n => (p : ℤ) ∣ a n) (i + Q + 1) - Nat.nth (fun n => (p : ℤ) ∣ a n) (i + Q) =
      Nat.nth (fun n => (p : ℤ) ∣ a n) (i + 1) - Nat.nth (fun n => (p : ℤ) ∣ a n) i :=
  fun p hp => ⟨infinitely_many p hp, gaps p hp⟩

end OMA.S_oeis_a377112

theorem OMA.solution : type_of% @OMA.S_oeis_a377112.main :=
  OMA.S_oeis_a377112.conjecture
