import OMAStatements.S_oeis_a115047
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# Prime indices of the Weil–Petersson volume numbers A115047

The published initial term a(3)=1 gives the single exception among the
prime indices in the domain. To treat every prime greater than 3, first
symmetrize the numerator. This proves that the integer division in the
definition is exact. The numerator at a prime p then contains a proper
interior binomial coefficient from row p in every summand, whereas
2(p−1) is prime to p.

Source: https://oeis.org/A115047. Credit: @Solitude1312
-/

open OMA.S_oeis_a115047

namespace OMA.A115047

private def halfTerm (m : ℕ) (f : ℕ → ℕ) (z : ℕ × ℕ) : ℕ :=
  m.choose z.1 * f z.1 * f z.2 * (z.2 + 1) * (m + 2).choose z.1

private lemma split_coefficient (m j k : ℕ) (hs : j + k = m) :
    (m + 4).choose (j + 2) * (j + 1) * (k + 1) =
      (m + 3) * ((k + 1) * (m + 2).choose j + (j + 1) * (m + 2).choose k) := by
  have hsym : (m + 3).choose (j + 2) = (m + 3).choose (k + 1) :=
    Nat.choose_symm_of_eq_add (by omega)
  have hpas : (m + 4).choose (j + 2) =
      (m + 3).choose (j + 1) + (m + 3).choose (k + 1) := by
    rw [Nat.choose_succ_succ' (m + 3) (j + 1), hsym]
  have hj := Nat.add_one_mul_choose_eq (m + 2) j
  have hk := Nat.add_one_mul_choose_eq (m + 2) k
  rw [hpas]
  calc
    _ = (k + 1) * ((m + 3) * (m + 2).choose j) +
        (j + 1) * ((m + 3) * (m + 2).choose k) := by rw [hj, hk]; ring
    _ = _ := by ring

private lemma integral_numerator (m : ℕ) (f : ℕ → ℕ) :
    numerator m f = 2 * (m + 3) * ∑ z ∈ Finset.antidiagonal m, halfTerm m f z := by
  calc
    numerator m f = ∑ z ∈ Finset.antidiagonal m,
        (m + 3) * (halfTerm m f z + halfTerm m f z.swap) := by
      apply Finset.sum_congr rfl
      rintro ⟨j, k⟩ hmem
      have hs : j + k = m := Finset.mem_antidiagonal.mp hmem
      have hsym : m.choose k = m.choose j := Nat.choose_symm_of_eq_add (by omega)
      dsimp [halfTerm]
      rw [hsym]
      calc
        _ = (m.choose j * f j * f k) * ((m + 4).choose (j + 2) * (j + 1) * (k + 1)) := by ring
        _ = _ := by rw [split_coefficient m j k hs]; ring
    _ = (m + 3) * ((∑ z ∈ Finset.antidiagonal m, halfTerm m f z) +
        ∑ z ∈ Finset.antidiagonal m, halfTerm m f z.swap) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [Finset.Nat.sum_antidiagonal_swap]; ring

/-- Recover exactly the rational recurrence in the source after clearing
its denominator. -/
lemma exact_recurrence (m : ℕ) : 2 * (m + 3) * b (m + 1) = numerator m b := by
  have hrec : b (m + 1) = numerator m b / (2 * (m + 3)) := by
    conv_lhs => rw [b]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    congr 1
    apply Finset.sum_congr rfl
    rintro ⟨j, k⟩ hmem
    have hs : j + k = m := Finset.mem_antidiagonal.mp hmem
    simp [show j < m + 1 by omega, show k < m + 1 by omega]
  rw [hrec, Nat.mul_comm]
  exact Nat.div_mul_cancel ⟨_, integral_numerator m b⟩

lemma larger_prime {p : ℕ} (hp : p.Prime) (h : 3 < p) : p ∣ b (p - 3) := by
  let m := p - 4
  have hm : p = m + 4 := by dsimp [m]; omega
  have hdiv : p ∣ numerator m b := by
    unfold numerator
    apply Finset.dvd_sum
    rintro ⟨j, k⟩ hmem
    have hs : j + k = m := Finset.mem_antidiagonal.mp hmem
    have hchoose := hp.dvd_choose_self (show j + 2 ≠ 0 by omega) (show j + 2 < p by omega)
    obtain ⟨t, ht⟩ := hchoose
    rw [hm] at ht
    change p ∣ m.choose j * (m + 4).choose (j + 2) * b j * b k * (j + 1) * (k + 1)
    rw [ht, ← hm]
    exact ⟨m.choose j * t * b j * b k * (j + 1) * (k + 1), by ring⟩
  rw [← exact_recurrence] at hdiv
  rcases hp.dvd_mul.mp hdiv with hd | hb
  · rcases hp.dvd_mul.mp hd with h2 | hpred
    · have := Nat.le_of_dvd (by decide : 0 < 2) h2
      omega
    · have := Nat.le_of_dvd (show 0 < m + 3 by omega) hpred
      omega
  · simpa only [show p - 3 = m + 1 by omega] using hb

lemma first_term : b 0 = 1 := by rw [b]; simp

/-- Three is exactly the exceptional prime among the published indices. -/
theorem classification (p : ℕ) (hdom : 3 ≤ p) (hp : p.Prime) :
    p ∣ b (p - 3) ↔ p ≠ 3 := by
  constructor
  · rintro hd rfl
    norm_num [first_term] at hd
  · intro h
    exact larger_prime hp (by omega)

end OMA.A115047

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a115047.main) := by
  intro h
  have bad := h 3 (by decide) (by decide)
  norm_num [OMA.A115047.first_term] at bad
