import OMAStatements.S_oeis_a121860
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open OMA.S_oeis_a121860

namespace DivisorSumResidue

lemma room (a b k : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hn : 2*k+4 ≤ a*b) :
    a+b+k ≤ a*b := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hb
  nlinarith [Nat.zero_le (u*v)]

lemma term_multiple (n a k : ℕ) (hn : 2*k+4 ≤ n) (ha : a ∈ n.divisors)
    (ha1 : a ≠ 1) (han : a ≠ n) : k.factorial ∣ term n a := by
  have prod : a*(n/a) = n := Nat.mul_div_cancel' (Nat.mem_divisors.mp ha).1
  have ha2 : 2 ≤ a := by have := Nat.pos_of_mem_divisors ha; omega
  have hb2 : 2 ≤ n/a := by
    have nonzero : n/a ≠ 0 := by
      intro h
      rw [h, mul_zero] at prod
      omega
    have nonunit : n/a ≠ 1 := by
      intro h
      rw [h, mul_one] at prod
      exact han prod
    exact (show ∀ m : ℕ, m ≠ 0 → m ≠ 1 → 2 ≤ m by omega) _ nonzero nonunit
  have bound : 2*k+4 ≤ a*(n/a) := by rwa [prod]
  have fit : a+n/a+k ≤ n := (room a (n/a) k ha2 hb2 bound).trans prod.le
  have hfac : (a.factorial*(n/a).factorial)*k.factorial ∣ n.factorial :=
    ((mul_dvd_mul_right (Nat.factorial_mul_factorial_dvd_factorial_add a (n/a)) k.factorial).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add (a+n/a) k)).trans
      (Nat.factorial_dvd_factorial fit)
  obtain ⟨w, hw⟩ := hfac
  unfold term
  rw [hw, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
  exact dvd_mul_right _ _

end DivisorSumResidue

open DivisorSumResidue

theorem OMA.solution : type_of% @OMA.S_oeis_a121860.main := by
  intro k hk
  refine ⟨2*k+4, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have h1 : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn0.ne'
  have hlast : n ∈ n.divisors.erase 1 :=
    Finset.mem_erase.mpr ⟨by omega, Nat.mem_divisors_self n hn0.ne'⟩
  have hsum : k ∣ ∑ d ∈ (n.divisors.erase 1).erase n, term n d := by
    apply Finset.dvd_sum
    intro d hd
    obtain ⟨hdn, hd⟩ := Finset.mem_erase.mp hd
    obtain ⟨hd1, hd⟩ := Finset.mem_erase.mp hd
    exact (Nat.dvd_factorial (by omega : 0 < k) (le_refl k)).trans (term_multiple n d k hn hd hd1 hdn)
  have e1 : term n 1 = 1 := by simp [term, Nat.div_self (Nat.factorial_pos n)]
  have en : term n n = 1 := by simp [term, Nat.div_self hn0, Nat.div_self (Nat.factorial_pos n)]
  unfold value
  rw [← Finset.sum_erase_add n.divisors (term n) h1,
      ← Finset.sum_erase_add (n.divisors.erase 1) (term n) hlast, e1, en, Nat.add_assoc]
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hsum]
  simp [Nat.mod_eq_of_lt (by omega : 2 < k)]
