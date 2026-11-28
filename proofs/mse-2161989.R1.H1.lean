import OMAReductions.R_mse_2161989_R1
import Mathlib

/-!
This proves the denominator descent proposed by @marcusbuffett in reduction
mse-2161989.R1 (PR #19889). The smaller denominator comes from the fundamental
Pell solution or its square, depending on which divisibility condition holds.
-/

open OMA.S_mse_2161989

private lemma oma_pell_minimum {p : ℕ} (hp : p.Prime) :
    0 < f p ∧ IsSquare (p * (f p)^2 + 1) := by
  have hd : ¬ IsSquare (p : ℤ) := fun h =>
    (Nat.prime_iff_prime_int.mp hp).not_isSquare h
  obtain ⟨a, _, hy⟩ := Pell.Solution₁.exists_pos_of_not_isSquare
    (show (0 : ℤ) < p by exact_mod_cast hp.pos) hd
  apply Nat.sInf_mem (s := {b : ℕ | 0 < b ∧ IsSquare (p*b^2+1)})
  refine ⟨a.y.toNat, by omega, ?_⟩
  apply Int.isSquare_natCast_iff.mp
  refine ⟨a.x, ?_⟩
  push_cast
  rw [Int.toNat_of_nonneg hy.le, ←sq, a.prop_x, add_comm]

private lemma oma_pell_descent
    (minimum : ∀ p : ℕ, p.Prime → 0 < f p ∧ IsSquare (p * (f p)^2 + 1)) :
    OMA.R_mse_2161989_R1.H1 := by
  intro p t hp ht hcase
  obtain ⟨hpos,a,ha⟩ := minimum p hp
  have descend (c x : ℕ) (hc : 0 < c) (hlt : c < f p)
      (hx : (p*t^2)*c^2+1=x*x) : f (p*t^2) < f p :=
    (Nat.sInf_le (show c ∈ {b : ℕ | 0 < b ∧ IsSquare ((p*t^2)*b^2+1)} from
      ⟨hc,x,hx⟩)).trans_lt hlt
  rcases hcase with hd | ⟨v,hv,htv,hd⟩
  · obtain ⟨c,heq⟩ := hd
    have hc : 0 < c := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at heq; omega
    apply descend c a hc
    · rw [heq]
      exact lt_mul_of_one_lt_left hc ht
    · rw [← ha, heq]
      ring
  · obtain ⟨c,heq⟩ := hd
    have hvpos : 0 < v := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hv
    have hc : 0 < c := by
      have hleft : 0 < 2*v*f p := by positivity
      rw [heq] at hleft
      exact Nat.pos_of_mul_pos_left hleft
    have hlt : c < f p := by
      by_contra! hle
      have h := Nat.mul_le_mul_left t hle
      have hstrict := Nat.mul_lt_mul_of_pos_right htv hpos
      omega
    apply descend c (2*p*(f p)^2+1) hc hlt
    calc
      (p*t^2)*c^2+1 = p*(t*c)^2+1 := by ring
      _ = p*(2*v*f p)^2+1 := by rw [← heq]
      _ = 4*p*(f p)^2*(v*v)+1 := by ring
      _ = (2*p*(f p)^2+1)*(2*p*(f p)^2+1) := by rw [← hv]; ring

theorem OMA.solution : OMA.R_mse_2161989_R1.H1 :=
  oma_pell_descent (fun _ => oma_pell_minimum)
