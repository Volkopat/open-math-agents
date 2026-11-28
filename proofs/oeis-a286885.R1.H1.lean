import OMAReductions.R_oeis_a286885_R1
import Mathlib

/-! Step oeis-a286885.R1.H1 (Fermat, Euler): a prime `p ≡ 1 (mod 3)` is `x² + 3y²`. An element
`ω` of order 3 in `(ZMod p)ˣ` (Cauchy) gives `(2ω+1)² = -3`. Thue's pigeonhole lemma gives
`|x|, |y| < √p` with `x ≡ (2ω+1) y`, so `p ∣ x² + 3y² < 4p`. The value `2p` is impossible
mod 4, and `3p` forces `3 ∣ x`. -/

namespace OMA.A286885H1

/-- `-3` is a square modulo a prime `p ≡ 1 (mod 3)`. -/
lemma exists_sq_neg_three (p : ℕ) [hp : Fact p.Prime] (h3 : p % 3 = 1) :
    ∃ a : ZMod p, a ^ 2 = -3 := by
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have hdvd : 3 ∣ Fintype.card (ZMod p)ˣ := by rw [hcard]; omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hdvd
  set w : ZMod p := (g : ZMod p)
  have hw3 : w ^ 3 = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    simpa [w] using congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) this
  have hw1 : w ≠ 1 := by
    intro h
    have : g = 1 := Units.ext (by simpa [w] using h)
    rw [this, orderOf_one] at hg
    norm_num at hg
  have hsum : w ^ 2 + w + 1 = 0 := by
    have : (w - 1) * (w ^ 2 + w + 1) = 0 := by ring_nf; rw [hw3]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hw1
    · exact h
  exact ⟨2 * w + 1, by linear_combination 4 * hsum⟩

/-- Thue's lemma: for `a` modulo `p` there are small `x, y`, not both zero, with `x ≡ a y`. -/
lemma thue (p : ℕ) [hp : Fact p.Prime] (a : ZMod p) :
    ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ x ^ 2 < p ∧ y ^ 2 < p ∧ ((x : ZMod p) = a * y) := by
  set s := Nat.sqrt p with hs
  have hs1 : p < (s + 1) * (s + 1) := Nat.lt_succ_sqrt p
  have hs2 : s * s ≤ p := Nat.sqrt_le p
  have hsq : s * s ≠ p := by
    intro h
    have := hp.out
    rw [← h] at this
    have hs1' : s ≠ 1 := by intro h1; rw [h1] at this; norm_num at this
    exact Nat.not_prime_mul hs1' hs1' this
  let f : Fin (s + 1) × Fin (s + 1) → ZMod p := fun uv => (uv.1 : ZMod p) - a * (uv.2 : ZMod p)
  have hcard : Fintype.card (ZMod p) < Fintype.card (Fin (s + 1) × Fin (s + 1)) := by
    simp only [ZMod.card, Fintype.card_prod, Fintype.card_fin]; exact hs1
  obtain ⟨⟨u, v⟩, ⟨u', v'⟩, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  refine ⟨(u : ℤ) - u', (v : ℤ) - v', ?_, ?_, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    apply hne
    have h1 : (u : ℕ) = u' := by omega
    have h2 : (v : ℕ) = v' := by omega
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · have hu := u.isLt; have hu' := u'.isLt
    have : |(u : ℤ) - u'| ≤ s := by rw [abs_le]; constructor <;> omega
    have : ((u : ℤ) - u') ^ 2 ≤ (s : ℤ) * s := by
      rw [← sq_abs, sq]; exact mul_le_mul this this (abs_nonneg _) (by positivity)
    have : (s : ℤ) * s < p := by exact_mod_cast lt_of_le_of_ne hs2 hsq
    linarith
  · have hv := v.isLt; have hv' := v'.isLt
    have : |(v : ℤ) - v'| ≤ s := by rw [abs_le]; constructor <;> omega
    have : ((v : ℤ) - v') ^ 2 ≤ (s : ℤ) * s := by
      rw [← sq_abs, sq]; exact mul_le_mul this this (abs_nonneg _) (by positivity)
    have : (s : ℤ) * s < p := by exact_mod_cast lt_of_le_of_ne hs2 hsq
    linarith
  · have : (u : ZMod p) - a * v = u' - a * v' := heq
    push_cast
    linear_combination this

theorem main (p : ℕ) (hp : p.Prime) (h3 : p % 3 = 1) : ∃ x y : ℕ, x ^ 2 + 3 * y ^ 2 = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_sq_neg_three p h3
  obtain ⟨x, y, hnz, hx, hy, hxy⟩ := thue p a
  -- `p ∣ x² + 3y²`
  have hdvd : (p : ℤ) ∣ x ^ 2 + 3 * y ^ 2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hxy]
    linear_combination (y : ZMod p) ^ 2 * ha
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < x ^ 2 + 3 * y ^ 2 := by
    rcases hnz with h | h
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg y]
    · have := pow_pos (abs_pos.2 h) 2; rw [sq_abs] at this; nlinarith [sq_nonneg x]
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hk0 : 0 < k := by
    by_contra hk0; push Not at hk0
    have : (p : ℤ) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0.le hk0
    linarith
  have hk4 : k < 4 := by
    by_contra hk4; push Not at hk4
    have : (p : ℤ) * 4 ≤ p * k := mul_le_mul_of_nonneg_left hk4 hp0.le
    linarith
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at h3
  have hpodd : (p : ℤ) % 2 = 1 := by
    have := hp.eq_two_or_odd; rcases this with h | h
    · exact absurd h hp2
    · exact_mod_cast h
  interval_cases k
  · exact ⟨x.natAbs, y.natAbs, by zify; rw [sq_abs, sq_abs]; linarith⟩
  · -- `x² + 3y² = 2p` is impossible modulo 4
    exfalso
    have h4 : (x ^ 2 + 3 * y ^ 2) % 4 = 0 ∨ (x ^ 2 + 3 * y ^ 2) % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one x with hx2 | hx2 <;>
        rcases Int.emod_two_eq_zero_or_one y with hy2 | hy2
      · left
        obtain ⟨x', rfl⟩ : 2 ∣ x := Int.dvd_of_emod_eq_zero hx2
        obtain ⟨y', rfl⟩ : 2 ∣ y := Int.dvd_of_emod_eq_zero hy2
        ring_nf; omega
      · right
        obtain ⟨x', rfl⟩ : 2 ∣ x := Int.dvd_of_emod_eq_zero hx2
        have : y = 2 * (y / 2) + 1 := by omega
        rw [this]; ring_nf; omega
      · right
        obtain ⟨y', rfl⟩ : 2 ∣ y := Int.dvd_of_emod_eq_zero hy2
        have : x = 2 * (x / 2) + 1 := by omega
        rw [this]; ring_nf; omega
      · left
        have e1 : x = 2 * (x / 2) + 1 := by omega
        have e2 : y = 2 * (y / 2) + 1 := by omega
        rw [e1, e2]; ring_nf; omega
    rw [hk] at h4
    omega
  · -- `x² + 3y² = 3p`: then `3 ∣ x`
    have h3x : (3 : ℤ) ∣ x := by
      have : (3 : ℤ) ∣ x ^ 2 := by
        have : x ^ 2 = 3 * (p - y ^ 2) := by linarith
        rw [this]; exact dvd_mul_right _ _
      exact Int.Prime.dvd_pow' (by norm_num) this
    obtain ⟨x', rfl⟩ := h3x
    refine ⟨y.natAbs, x'.natAbs, ?_⟩
    zify; rw [sq_abs, sq_abs]; linarith
end OMA.A286885H1

theorem OMA.solution : OMA.R_oeis_a286885_R1.H1 :=
  fun p hp h3 => OMA.A286885H1.main p hp h3
