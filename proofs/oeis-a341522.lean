import OMAStatements.S_oeis_a341522
import Mathlib

open OMA.S_oeis_a341522

theorem OMA.solution : type_of% @OMA.S_oeis_a341522.main := by
  intro ps d inv h1 h2 d1 de dodd hinv n
  have hpow : ∀ v x : ℕ, 1 ≤ x → d (2 ^ v * x) = 2 ^ v * d x := by
    intro v
    induction v with
    | zero => intro x _; simp
    | succ v ih =>
      intro x hx
      have hpos : 1 ≤ 2 ^ v * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have e : 2 ^ (v + 1) * x = 2 * (2 ^ v * x) := by ring
      rw [e, de _ hpos, ih x hx]
      ring
  have hodd : ∀ i : ℕ, d (2 * (2 * i + 1) + 1) = 3 * d (2 * i + 1) := by
    intro i
    rw [dodd, dodd i]
    have : 2 * i + 1 + 1 = 2 * (i + 1) := by ring
    rw [this, de _ (by omega), h2]
  have hN0 : n + 1 ≠ 0 := by omega
  have hpd : 2 ^ padicValNat 2 (n + 1) ∣ n + 1 := pow_padicValNat_dvd
  have hnd : ¬ 2 ^ (padicValNat 2 (n + 1) + 1) ∣ n + 1 := pow_succ_padicValNat_not_dvd hN0
  generalize padicValNat 2 (n + 1) = v at hpd hnd ⊢
  obtain ⟨o, ho⟩ := hpd
  have hoodd : ¬ 2 ∣ o := by
    rintro ⟨c, rfl⟩
    exact hnd ⟨c, by rw [ho]; ring⟩
  obtain ⟨i, rfl⟩ : ∃ i, o = 2 * i + 1 := ⟨o / 2, by omega⟩
  have key : d (2 ^ v * (2 * (2 * i + 1) + 1)) = 3 * d (n + 1) := by
    rw [hpow v (2 * (2 * i + 1) + 1) (by omega), hodd, ho, hpow v (2 * i + 1) (by omega)]
    ring
  rw [← key, hinv _ (Nat.one_le_iff_ne_zero.mpr (by positivity))]
  have : 2 ^ v * (2 * (2 * i + 1) + 1) = 2 * (n + 1) + 2 ^ v := by
    rw [ho]; ring
  rw [this]
  omega
