import FormalConjectures.ErdosProblems.«939»

-- Shorter proof of Erdos939.erdos_939.variants.triples
-- Credit: @B221393

theorem OMA.solution : type_of% @Erdos939.erdos_939.variants.triples := by
  have hf : ∀ a b, (3 : ℕ).Full b → (3 : ℕ).Full (a ^ 3 * b) := fun a b hb p hp => by
    obtain ⟨hp, hd, hn⟩ := Nat.mem_primeFactors.mp hp
    rcases hp.dvd_mul.mp hd with h | h
    · exact (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow h) 3).mul_right _
    · exact (hb p (Nat.mem_primeFactors.mpr ⟨hp, h, right_ne_zero_of_mul hn⟩)).mul_left _
  have hf3 (a : ℕ) : (3 : ℕ).Full (a ^ 3) := by simpa using hf a 1 (by simp [Nat.Full])
  have grow : ∀ N : ℕ, ∃ x y : ℤ, IsCoprime x y ∧ (x : ZMod 6) = 5 ∧ (y : ZMod 6) = 1 ∧
      (3 : ℕ).Full (x ^ 3 + y ^ 3).natAbs ∧ N < (x ^ 3 + y ^ 3).natAbs := by
    intro N
    induction N with
    | zero =>
      refine ⟨-271, 919, by decide, by decide, by decide, ?_, by decide⟩
      change (3 : ℕ).Full (146 ^ 3 * 3 ^ 3 * 9)
      have h243 : (3 : ℕ).Full (3 ^ 5) := fun p hp => by
        obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hp
        have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd)
        subst h3; exact pow_dvd_pow 3 (by decide)
      simpa [show (146 ^ 3 * 3 ^ 3 * 9 : ℕ) = 146 ^ 3 * 3 ^ 5 by norm_num] using hf 146 (3 ^ 5) h243
    | succ N ih =>
      obtain ⟨x, y, hxy, hx, hy, hfc, hN⟩ := ih
      let A := x ^ 3 + 2 * y ^ 3
      let B := 2 * x ^ 3 + y ^ 3
      have hAy : IsCoprime A y := by
        rw [show A = x ^ 3 + y * (2 * y ^ 2) by dsimp [A]; ring]
        exact hxy.pow_left.add_mul_left_left _
      have heq : ((x * A) ^ 3 + (-y * B) ^ 3).natAbs =
          (x ^ 3 - y ^ 3).natAbs ^ 3 * (x ^ 3 + y ^ 3).natAbs := by
        rw [← Int.natAbs_pow, ← Int.natAbs_mul]; congr 1; dsimp [A, B]; ring
      have hD := (ZMod.intCast_eq_intCast_iff' (x ^ 3 - y ^ 3) 4 6).mp (by simp [hx, hy]; decide)
      refine ⟨x * A, -y * B, ?_, by simp [A, hx, hy]; decide, by simp [B, hx, hy]; decide,
        heq ▸ hf _ _ hfc, ?_⟩
      · rw [neg_mul, IsCoprime.neg_right_iff]
        refine (hxy.mul_right ?_).mul_left (hAy.mul_right ?_)
        · rw [show B = y ^ 3 + x * (2 * x ^ 2) by dsimp [B]; ring]
          exact hxy.pow_right.add_mul_left_right _
        · have := (ZMod.intCast_eq_intCast_iff' A 1 6).mp (by simp [A, hx, hy]; decide)
          rw [show B = 2 * A - 3 * y ^ 3 by dsimp [A, B]; ring, IsCoprime.mul_sub_right_right_iff]
          have hA3 : IsCoprime A 3 := ⟨1, -(2 * (A / 6)), by omega⟩
          exact hA3.mul_right hAy.pow_right
      · rw [heq]
        nlinarith [Nat.pow_le_pow_left (show 2 ≤ (x ^ 3 - y ^ 3).natAbs by omega) 3]
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image (fun t : ℕ × ℕ × ℕ => t.2.2)).bddAbove
  obtain ⟨x, y, hc, hx, hy, hfc, hN⟩ := grow M
  let a := x.natAbs ^ 3
  let b := y.natAbs ^ 3
  let c := (x ^ 3 + y ^ 3).natAbs
  have ha : 0 < a := by by_contra h; simp [a] at h; rw [h] at hx; revert hx; decide
  have hb : 0 < b := by by_contra h; simp [b] at h; rw [h] at hy; revert hy; decide
  have hcp : ∀ {S : Finset ℕ}, a ∈ S → b ∈ S → S.Coprime := fun ha' hb' =>
    Nat.dvd_one.mp (((Int.isCoprime_iff_nat_coprime.mp hc).pow 3 3).gcd_eq_one ▸
      Nat.dvd_gcd (Finset.gcd_dvd ha') (Finset.gcd_dvd hb'))
  have h : a + b = c ∨ a + c = b ∨ b + c = a := by
    dsimp [a, b, c]; rw [← Int.natAbs_pow, ← Int.natAbs_pow]; omega
  rcases h with h | h | h
  · have := hM ⟨(a, b, c), ⟨hcp (by simp) (by simp), ha, hb, hf3 _, hf3 _, hfc, h⟩, rfl⟩
    dsimp only at this; omega
  · have := hM ⟨(a, c, b), ⟨hcp (by simp) (by simp), ha, by omega, hf3 _, hfc, hf3 _, h⟩, rfl⟩
    dsimp only at this; omega
  · have := hM ⟨(b, c, a), ⟨hcp (by simp) (by simp), hb, by omega, hf3 _, hfc, hf3 _, h⟩, rfl⟩
    dsimp only at this; omega
