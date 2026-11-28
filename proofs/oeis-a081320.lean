import OMAStatements.S_oeis_a081320

-- Problem: A081320, the 3-smooth part of F(n) has period 12 off multiples of 12.
-- Credit: @bnb9001

namespace OMA_A081320_Proof

open OMA.S_oeis_a081320

theorem fib_add12 (k : ℕ) : Nat.fib (k + 12) = 89 * Nat.fib k + 144 * Nat.fib (k + 1) := by
  have := Nat.fib_add 11 k
  rw [show 11 + k + 1 = k + 12 by ring] at this
  rw [this]; norm_num [Nat.fib_add_two]

theorem fib_add24_mod (k : ℕ) : Nat.fib (k + 24) % 144 = Nat.fib k % 144 := by
  have := Nat.fib_add 23 k
  rw [show 23 + k + 1 = k + 24 by ring] at this
  rw [this]
  have h23 : Nat.fib 23 = 28657 := by decide
  have h24 : Nat.fib 24 = 46368 := by decide
  rw [h23, h24]
  omega

theorem fib_mod144 (k : ℕ) : Nat.fib k % 144 = Nat.fib (k % 24) % 144 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 24 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 24 := ⟨k - 24, by omega⟩
      rw [fib_add24_mod, ih j (by omega), show (j + 24) % 24 = j % 24 by omega]

theorem small (r : ℕ) (hr : r < 24) (h12 : r % 12 ≠ 0) :
    Nat.fib r % 16 ≠ 0 ∧ Nat.fib r % 9 ≠ 0 := by
  interval_cases r <;> simp_all <;> decide

theorem not16 (k : ℕ) (h : k % 12 ≠ 0) : ¬ 2 ^ 4 ∣ Nat.fib k := by
  intro hd
  have h1 := fib_mod144 k
  have h2 := (small (k % 24) (Nat.mod_lt _ (by norm_num)) (by omega)).1
  omega

theorem not9 (k : ℕ) (h : k % 12 ≠ 0) : ¬ 3 ^ 2 ∣ Nat.fib k := by
  intro hd
  have h1 := fib_mod144 k
  have h2 := (small (k % 24) (Nat.mod_lt _ (by norm_num)) (by omega)).2
  omega

theorem v_eq (p B u c x y : ℕ) (hp : p.Prime) (hB : p ^ B ∣ c) (hu : Nat.Coprime p u) (hu0 : 0 < u)
    (hx : ¬ p ^ B ∣ x) : padicValNat p (u * x + c * y) = padicValNat p x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (dvd_zero _)
  have hs0 : u * x + c * y ≠ 0 := by positivity
  have key : ∀ i ≤ B, p ^ i ∣ u * x + c * y ↔ p ^ i ∣ x := by
    intro i hi
    have hc : p ^ i ∣ c * y := dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow p hi) hB) y
    rw [Nat.dvd_add_left hc]
    exact (Nat.Coprime.pow_left i hu).dvd_mul_left
  have hjB : padicValNat p x < B := by
    by_contra hge
    exact hx (dvd_trans (pow_dvd_pow p (not_lt.mp hge)) pow_padicValNat_dvd)
  apply le_antisymm
  · by_contra hlt
    rw [not_le] at hlt
    have h1 : p ^ (padicValNat p x + 1) ∣ u * x + c * y :=
      (padicValNat_dvd_iff_le hs0).mpr hlt
    rw [key _ (by omega), padicValNat_dvd_iff_le hx0] at h1
    omega
  · rw [← padicValNat_dvd_iff_le hs0, key _ hjB.le]
    exact pow_padicValNat_dvd

end OMA_A081320_Proof

open OMA.S_oeis_a081320 OMA_A081320_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a081320.main := by
  intro n hn h12
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 12 := ⟨n - 12, by omega⟩
  have hk : k % 12 ≠ 0 := by omega
  unfold a smooth3Part
  rw [Nat.add_sub_cancel, fib_add12, Nat.factorization_def _ Nat.prime_two,
    Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_two,
    Nat.factorization_def _ Nat.prime_three,
    v_eq 2 4 89 144 _ _ Nat.prime_two (by norm_num) (by norm_num) (by norm_num) (not16 k hk),
    v_eq 3 2 89 144 _ _ Nat.prime_three (by norm_num) (by norm_num) (by norm_num) (not9 k hk)]
