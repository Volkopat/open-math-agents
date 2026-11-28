import OMAReductions.R_Idoneal_idoneal_numbers_completeness_R2

open Idoneal

private def SmallWitness (n : ℕ) : Prop :=
  ∃ d : Fin 64, ∃ a : Fin 32,
    let b := d.val - a.val
    let c := (n - a.val * b) / d.val
    0 < a.val ∧ a.val < b ∧ b < c ∧ n = a.val * b + b * c + a.val * c

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
/-- For the small multiplier primes, search only the sum and the smaller
member of the first pair. The last member is determined by the equation. -/
private theorem verifySmall : ∀ (m : knownIdonealNumbers) (p : Fin 44),
    p.val.Prime → p.val ^ 2 * m.val ∉ knownIdonealNumbers →
    SmallWitness (p.val ^ 2 * m.val) := by
  unfold SmallWitness
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
/-- A small odd prime at which the negative base is a nonzero square. -/
private theorem verifySeeds : ∀ m : knownIdonealNumbers, 0 < m.val ∧
    ∃ q : Fin 44, q.val.Prime ∧ Odd q.val ∧ ∃ s : Fin 44,
      0 < s.val ∧ s.val < q.val ∧ q.val ∣ m.val + s.val ^ 2 := by
  decide +kernel

/-- Use the two complementary representatives of a nonzero square root
as the first pair, and solve for the third member. -/
private theorem extendFromSeed {m p q s : ℕ} (hm : 0 < m)
    (hp : p.Prime) (hq : q.Prime) (hodd : Odd q)
    (hqp : q < p) (hs : 0 < s) (hsq : s < q)
    (hseed : q ∣ m + s ^ 2) :
    ∃ a b c : ℕ, 0 < a ∧ a < b ∧ b < c ∧ p ^ 2 * m = a * b + b * c + a * c := by
  let r := (p * s) % q
  have hrq : r < q := Nat.mod_lt _ hq.pos
  have hr : 0 < r := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hd : q ∣ p * s := Nat.dvd_iff_mod_eq_zero.mpr hzero
    rcases hq.dvd_mul.mp hd with h | h
    · rcases (Nat.dvd_prime hp).mp h with h | h
      · exact hq.ne_one h
      · omega
    · exact (not_le_of_gt hsq) (Nat.le_of_dvd hs h)
  have hd : q ∣ p ^ 2 * m + r ^ 2 := by
    have hscaled : q ∣ p ^ 2 * m + (p * s) ^ 2 := by
      rw [mul_pow, ← mul_add]
      exact dvd_mul_of_dvd_right hseed (p ^ 2)
    have hsame : r ≡ p * s [MOD q] := Nat.mod_modEq _ _
    exact Nat.modEq_zero_iff_dvd.mp
      (((Nat.ModEq.refl (p ^ 2 * m)).add (hsame.pow 2)).trans
        (Nat.modEq_zero_iff_dvd.mpr hscaled))
  let a := min r (q - r)
  let b := max r (q - r)
  have hpair : a + b = q := by dsimp [a, b]; omega
  have ha : 0 < a := by dsimp [a]; omega
  have hab : a < b := by
    obtain ⟨k, hk⟩ := hodd
    dsimp [a, b]
    omega
  have hprod : a * b = r * (q - r) := by
    rcases le_total r (q - r) with h | h
    · simp only [a, b, min_eq_left h, max_eq_right h]
    · simp only [a, b, min_eq_right h, max_eq_left h, Nat.mul_comm (q - r) r]
  have hsumSquares : a * b + r ^ 2 = q * r := by
    calc
      _ = (q - r + r) * r := by rw [hprod]; ring
      _ = q * r := by rw [Nat.sub_add_cancel hrq.le]
  have hlimit : a * b + q * b ≤ q * q := by
    rw [← hpair]
    nlinarith only [Nat.zero_le (a * a)]
  have hlarge : q * q < p ^ 2 * m := by
    calc
      q * q < p * q := Nat.mul_lt_mul_of_pos_right hqp hq.pos
      _ < p * p := Nat.mul_lt_mul_of_pos_left hqp hp.pos
      _ ≤ p ^ 2 * m := by
        rw [pow_two]
        simpa using Nat.mul_le_mul_left (p * p) hm
  have hrest : q ∣ p ^ 2 * m - a * b := by
    have hsub : (p ^ 2 * m + r ^ 2) - q * r = p ^ 2 * m - a * b := by omega
    rw [← hsub]
    exact Nat.dvd_sub hd (dvd_mul_right q r)
  obtain ⟨c, hc⟩ := hrest
  have hbq : q * b < q * c := by omega
  have hbc : b < c := by
    by_contra! h
    exact (not_le_of_gt hbq) (Nat.mul_le_mul_left q h)
  have hqc : q * c = b * c + a * c := by rw [← hpair]; ring
  exact ⟨a, b, c, ha, hab, hbc, by omega⟩

theorem OMA.solution : OMA.R_Idoneal_idoneal_numbers_completeness_R2.H2 := by
  intro m hm p hp hmiss
  by_cases hpSmall : p < 44
  · obtain ⟨d, a, h⟩ := verifySmall ⟨m, hm⟩ ⟨p, hpSmall⟩ hp hmiss
    exact ⟨a.val, d.val - a.val, (p ^ 2 * m - a.val * (d.val - a.val)) / d.val, h⟩
  · obtain ⟨hm0, q, hq, hqOdd, s, hs, hsq, hseed⟩ := verifySeeds ⟨m, hm⟩
    exact extendFromSeed hm0 hp hq hqOdd (lt_of_lt_of_le q.isLt (le_of_not_gt hpSmall))
      hs hsq hseed
