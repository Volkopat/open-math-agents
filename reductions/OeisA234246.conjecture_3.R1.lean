import FormalConjectures.OEIS.«234246»
import Mathlib

/- A product of distinct primes p*q has cototient p+q-1. A square just below n
of the opposite parity makes the required sum p+q even, while the upper bound
on the smaller prime keeps the product below n. -/

namespace OMA.R_OeisA234246_conjecture_3_R1

/-- The bounded part can be checked by constructing witnesses. -/
def H1 : Prop := ∀ n : ℕ, 60 ≤ n → n < 2 ^ 20 →
  ∃ k, 0 < k ∧ k < n ∧ IsSquare (k + (n - k).totient)

/-- A quantitative binary Goldbach statement. The fixed allowance includes
small even numbers for which a prime below one sixteenth is unavailable. -/
def H2 : Prop := ∀ e : ℕ, 8 ≤ e → Even e →
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p + q = e ∧ (p ≤ 128 ∨ 16 * p < e)

lemma witness {n m r : ℕ} (hm : 0 < m) (hmn : m < n)
    (h : n + m.totient = r * r + m) :
    ∃ k, 0 < k ∧ k < n ∧ IsSquare (k + (n - k).totient) := by
  refine ⟨n - m, by omega, by omega, r, ?_⟩
  rw [show n - (n - m) = m by omega]
  omega

lemma totient_product {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) :
    (p * q).totient + p + q = p * q + 1 := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 h), Nat.totient_prime hp, Nat.totient_prime hq]
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne_zero
  simp only [Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

lemma odd_gap {n : ℕ} (hn : 2 ^ 20 ≤ n) :
    ∃ r d : ℕ, 640 ≤ r ∧ n = r * r + d ∧ d % 2 = 1 ∧ d ≤ 4 * r + 3 := by
  let s := n.sqrt
  have hlo : s * s ≤ n := Nat.sqrt_le n
  have hhi : n < (s + 1) * (s + 1) := Nat.lt_succ_sqrt n
  have hs : 641 ≤ s := by
    by_contra! h
    have hb := Nat.mul_le_mul (show s + 1 ≤ 641 by omega) (show s + 1 ≤ 641 by omega)
    norm_num at hn hb
    omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (show s ≠ 0 by omega)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlo
  by_cases ho : d % 2 = 1
  · refine ⟨s, d, by omega, hd, ho, ?_⟩
    nlinarith
  · refine ⟨r, d + 2 * r + 1, by omega, ?_, by omega, ?_⟩ <;>
      rw [hr] at hd hhi <;> nlinarith

theorem main : H1 → H2 → type_of% @OeisA234246.conjecture_3 := by
  intro hfinite hgold n hn
  by_cases hb : n < 2 ^ 20
  · exact hfinite n hn hb
  obtain ⟨r, d, hr, hnd, hodd, hsize⟩ := odd_gap (Nat.le_of_not_gt hb)
  by_cases hsmall : d < 7
  · have hd : d = 1 ∨ d = 3 ∨ d = 5 := by omega
    rcases hd with hd | hd | hd
    · apply witness (m := 2) (r := r) (by decide) (by omega)
      rw [show Nat.totient 2 = 1 by decide]
      omega
    · apply witness (m := 9) (r := r) (by decide) (by omega)
      rw [show Nat.totient 9 = 6 by decide]
      omega
    · apply witness (m := 25) (r := r) (by decide) (by omega)
      rw [show Nat.totient 25 = 20 by decide]
      omega
  obtain ⟨p, q, hp, hq, hpq, hsum, hbal⟩ :=
    hgold (d + 1) (by omega) ⟨(d + 1) / 2, by omega⟩
  have hprod : p * q ≤ r * r := by
    by_cases h : p ≤ 128
    · calc
        p * q ≤ p * (5 * r) := Nat.mul_le_mul_left _ (by omega)
        _ = (5 * p) * r := by ring
        _ ≤ r * r := Nat.mul_le_mul_right _ (by omega)
    · calc
        p * q ≤ p * (4 * r) := Nat.mul_le_mul_left _ (by omega)
        _ = (4 * p) * r := by ring
        _ ≤ r * r := Nat.mul_le_mul_right _ (by omega)
  apply witness (m := p * q) (r := r) (Nat.mul_pos hp.pos hq.pos) (by omega)
  have hphi := totient_product hp hq hpq
  omega

end OMA.R_OeisA234246_conjecture_3_R1
