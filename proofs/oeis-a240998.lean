import OMAStatements.S_oeis_a240998
import Mathlib

open PowerSeries

namespace P240998

theorem two_eq : (2 : ZMod 2) = 0 := rfl

theorem sq_coeff (B : PowerSeries (ZMod 2)) (n : ℕ) :
    coeff n (B ^ 2) = if n % 2 = 0 then coeff (n / 2) B else 0 := by
  rw [sq, coeff_mul]
  split_ifs with hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hmem : (m, m) ∈ Finset.HasAntidiagonal.antidiagonal (2 * m) := by simp; ring
    rw [← Finset.add_sum_erase _ _ hmem]
    have hz : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (2 * m)).erase (m, m), coeff x.1 B * coeff x.2 B = 0 := by
      apply Finset.sum_involution (fun x _ => (x.2, x.1))
      · intro a _
        rw [mul_comm (coeff a.2 B), ← two_mul, two_eq, zero_mul]
      · intro a ha _ heq
        simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        have e1 := congrArg Prod.fst heq
        have e2 := congrArg Prod.snd heq
        simp only at e1 e2
        apply ha.1
        ext <;> simp <;> omega
      · intro a ha
        simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at ha ⊢
        refine ⟨fun h => ha.1 (by ext <;> simp <;> omega), by omega⟩
      · intro a _; rfl
    rw [hz, add_zero, show 2 * m / 2 = m by omega]
    have : ∀ x : ZMod 2, x * x = x := by decide
    exact this _
  · apply Finset.sum_involution (fun x _ => (x.2, x.1))
    · intro a _
      rw [mul_comm (coeff a.2 B), ← two_mul, two_eq, zero_mul]
    · intro a ha _ heq
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
      have e1 := congrArg Prod.fst heq
      have e2 := congrArg Prod.snd heq
      simp only at e1 e2
      omega
    · intro a ha
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
      exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp only; omega)
    · intro a _; rfl

theorem pow2 (n : ℕ) (hn : 1 ≤ n) (b : ℕ → ZMod 2)
    (hb : ∀ n, 1 ≤ n → b n = (if n % 2 = 0 then b (n / 2) else 0) - (if n = 1 then 1 else 0)) :
    b n = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [hb n hn]
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have : n = 1 := by omega
      subst this
      rw [if_neg (by norm_num), if_pos rfl]
      constructor
      · intro _; exact ⟨0, rfl⟩
      · intro _; decide
    · rw [if_neg (show n ≠ 1 by omega), sub_zero]
      split_ifs with he
      · rw [ih (n / 2) (by omega) (by omega)]
        constructor
        · rintro ⟨k, hk⟩; exact ⟨k + 1, by rw [pow_succ]; omega⟩
        · rintro ⟨k, hk⟩
          rcases k with _ | k
          · simp at hk; omega
          · exact ⟨k, by rw [pow_succ] at hk; omega⟩
      · constructor
        · intro h; exact absurd h (by decide)
        · rintro ⟨k, hk⟩
          rcases k with _ | k
          · simp at hk; omega
          · rw [pow_succ] at hk; omega

end P240998

theorem OMA.solution : type_of% @OMA.S_oeis_a240998.main := by
  intro A hA hE n hn
  set φ := Int.castRingHom (ZMod 2)
  set B := A.map φ with hBdef
  have hs : HasSubst (X + 2 * X ^ 2 : PowerSeries ℤ) := HasSubst.of_constantCoeff_zero' (by simp)
  have hq : (X + 2 * X ^ 2 : PowerSeries ℤ).map φ = X := by
    simp only [map_add, map_mul, map_pow, map_X]
    rw [show (2 : PowerSeries ℤ) = C 2 by simp, map_C]
    simp [φ, P240998.two_eq]
  have hE' : B ^ 2 = X + B := by
    have := congrArg (map φ) hE
    rw [map_pow, map_add, map_X] at this
    have hm := map_subst hs (h := φ) A
    erw [hm] at this
    rw [hBdef, this]
    congr 1
    erw [hq]
    exact X_subst _
  have hb : ∀ m, 1 ≤ m → coeff m B = (if m % 2 = 0 then coeff (m / 2) B else 0) - (if m = 1 then 1 else 0) := by
    intro m hm
    have := congrArg (coeff m) hE'
    rw [P240998.sq_coeff, map_add, coeff_X] at this
    rw [this]
    split_ifs <;> ring
  have key := P240998.pow2 n hn (fun m => coeff m B) hb
  rw [← key, hBdef, coeff_map]
  exact ZMod.intCast_eq_one_iff_odd.symm
