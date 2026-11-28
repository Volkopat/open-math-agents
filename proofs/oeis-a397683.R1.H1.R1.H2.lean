import OMAReductions.R_oeis_a397683_R1_H1_R1
import Mathlib

/-! Hensel-type lift: among `y = x + k p` with `k = 0, 1, 2`, at most one `k` makes
`y ^ d ≡ 1 (mod p²)` and at most one makes `(y + 1) ^ d ≡ 1 (mod p²)`, because
`(x + k p) ^ d ≡ x ^ d + d x^(d-1) k p (mod p²)` and `d x^(d-1)` is a unit mod `p`. -/

namespace OMA.Step_oeis_a397683_R1_H1_R1_H2

/-- For `x ^ d - 1 = p s`, the lift `x + k p` has
`(x + k p) ^ d - x ^ d ≡ p (x^(d-1) d k) (mod p²)`. -/
theorem lift_mod (p x k : ℤ) (n : ℕ) :
    p ^ 2 ∣ (x + k * p) ^ n - x ^ n - p * (x ^ (n - 1) * n * k) := by
  have h := sq_dvd_add_pow_sub_sub (k * p) x n
  have h2 : p ^ 2 ∣ (k * p) ^ 2 := ⟨k ^ 2, by ring⟩
  obtain ⟨c, hc⟩ := dvd_trans h2 h
  exact ⟨c, by linear_combination hc⟩

theorem main (p x d : ℕ) (hp : p.Prime) (hodd : Odd p) (hx1 : 1 ≤ x) (hxp : x + 1 < p)
    (hd : d ≠ 0) (ho : orderOf (x : ZMod p) = d) (ho' : orderOf ((x + 1 : ℕ) : ZMod p) = d) :
    ∃ y t u : ℕ, 1 ≤ y ∧ y < p ^ 2 ∧ y ≡ x [MOD p] ∧ y ^ d = 1 + p * t ∧
      (y + 1) ^ d = 1 + p * u ∧ ¬ (p : ℤ) ∣ (t : ℤ) ∧ ¬ (p : ℤ) ∣ (u : ℤ) := by
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by
    rcases hodd with ⟨m, hm⟩
    omega
  have hx0 : (x : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hx0' : ((x + 1 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hdp : d ∣ p - 1 := ho ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have hdlt : d < p := by
    have := Nat.le_of_dvd (by omega) hdp
    omega
  have hd0 : (d : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hxd : (x : ZMod p) ^ d = 1 := ho ▸ pow_orderOf_eq_one _
  have hxd' : ((x : ZMod p) + 1) ^ d = 1 := by
    have := ho' ▸ pow_orderOf_eq_one ((x + 1 : ℕ) : ZMod p)
    exact_mod_cast this
  have hs : (p : ℤ) ∣ (x : ℤ) ^ d - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hxd, sub_self]
  have hs' : (p : ℤ) ∣ ((x : ℤ) + 1) ^ d - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hxd', sub_self]
  obtain ⟨s, hs⟩ := hs
  obtain ⟨s', hs'⟩ := hs'
  set c : ZMod p := (x : ZMod p) ^ (d - 1) * d with hc
  set c' : ZMod p := ((x : ZMod p) + 1) ^ (d - 1) * d with hc'
  have hc0 : c ≠ 0 := mul_ne_zero (pow_ne_zero _ hx0) hd0
  have hc0' : c' ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ ?_) hd0
    exact_mod_cast hx0'
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  have h02 : (0 : ZMod p) ≠ 2 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h.symm
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have h12 : (1 : ZMod p) ≠ 2 := by
    intro h
    have : ((1 : ℕ) : ZMod p) = 0 := by
      have : (2 : ZMod p) - 1 = 0 := by rw [← h]; ring
      exact_mod_cast (by linear_combination this : (1 : ZMod p) = 0)
    rw [ZMod.natCast_eq_zero_iff] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  have r : ∀ (e f : ZMod p), f ≠ 0 → ∀ a b : ZMod p, e + f * a = 0 → e + f * b = 0 → a = b := by
    intro e f hf a b ha hb
    have : f * (a - b) = 0 := by linear_combination ha - hb
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hf
    · exact sub_eq_zero.mp h
  obtain ⟨k, hk3, hgood, hgood'⟩ : ∃ k : ℕ, k ≤ 2 ∧ (s : ZMod p) + c * k ≠ 0 ∧
      (s' : ZMod p) + c' * k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have e0 := hcon 0 (by omega)
    have e1 := hcon 1 (by omega)
    have e2 := hcon 2 (by omega)
    push_cast at e0 e1 e2
    by_cases a0 : (s : ZMod p) + c * 0 = 0
    · by_cases a1 : (s : ZMod p) + c * 1 = 0
      · exact h01 (r _ _ hc0 _ _ a0 a1)
      · by_cases a2 : (s : ZMod p) + c * 2 = 0
        · exact h02 (r _ _ hc0 _ _ a0 a2)
        · exact h12 (r _ _ hc0' _ _ (e1 a1) (e2 a2))
    · by_cases a1 : (s : ZMod p) + c * 1 = 0
      · by_cases a2 : (s : ZMod p) + c * 2 = 0
        · exact h12 (r _ _ hc0 _ _ a1 a2)
        · exact h02 (r _ _ hc0' _ _ (e0 a0) (e2 a2))
      · exact h01 (r _ _ hc0' _ _ (e0 a0) (e1 a1))
  have hyd : 1 ≤ (x + k * p) ^ d := Nat.one_le_pow _ _ (by omega)
  have hyd' : 1 ≤ (x + k * p + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hdvd : p ∣ (x + k * p) ^ d - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hyd]
    push_cast
    rw [ZMod.natCast_self, mul_zero, add_zero, hxd, sub_self]
  have hdvd' : p ∣ (x + k * p + 1) ^ d - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hyd']
    push_cast
    rw [ZMod.natCast_self, mul_zero, add_zero, hxd', sub_self]
  obtain ⟨t, ht⟩ := hdvd
  obtain ⟨u, hu⟩ := hdvd'
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨x + k * p, t, u, by omega, ?_, ?_, by omega, by omega, ?_, ?_⟩
  · have : k * p ≤ 2 * p := Nat.mul_le_mul_right _ hk3
    have : 3 * p ≤ p * p := Nat.mul_le_mul_right _ hp3
    rw [pow_two]; omega
  · simp [Nat.ModEq, Nat.add_mul_mod_self_right]
  · intro htd
    obtain ⟨m, hm⟩ := htd
    obtain ⟨q, hq⟩ := lift_mod (p : ℤ) (x : ℤ) (k : ℤ) d
    have hyt : (((x + k * p) ^ d : ℕ) : ℤ) = 1 + p * t := by
      have : (x + k * p) ^ d = 1 + p * t := by omega
      exact_mod_cast this
    push_cast at hyt
    have e2 : s + (x : ℤ) ^ (d - 1) * d * k = p * (m - q) := by
      apply mul_left_cancel₀ hp0
      linear_combination hyt - hq - hs + (p : ℤ) * hm
    apply hgood
    have : ((s + (x : ℤ) ^ (d - 1) * d * k : ℤ) : ZMod p) = 0 := by
      rw [e2]; push_cast; simp
    push_cast at this
    rw [hc]; linear_combination this
  · intro hud
    obtain ⟨m, hm⟩ := hud
    obtain ⟨q, hq⟩ := lift_mod (p : ℤ) ((x : ℤ) + 1) (k : ℤ) d
    have hyt : (((x + k * p + 1) ^ d : ℕ) : ℤ) = 1 + p * u := by
      have : (x + k * p + 1) ^ d = 1 + p * u := by omega
      exact_mod_cast this
    push_cast at hyt
    have e2 : s' + ((x : ℤ) + 1) ^ (d - 1) * d * k = p * (m - q) := by
      apply mul_left_cancel₀ hp0
      linear_combination hyt - hq - hs' + (p : ℤ) * hm
    apply hgood'
    have : ((s' + ((x : ℤ) + 1) ^ (d - 1) * d * k : ℤ) : ZMod p) = 0 := by
      rw [e2]; push_cast; simp
    push_cast at this
    rw [hc']; linear_combination this

end OMA.Step_oeis_a397683_R1_H1_R1_H2

theorem OMA.solution : OMA.R_oeis_a397683_R1_H1_R1.H2 :=
  fun p x d hp ho hx1 hxp hd h1 h2 =>
    OMA.Step_oeis_a397683_R1_H1_R1_H2.main p x d hp ho hx1 hxp hd h1 h2
