import OMAStatements.S_oeis_a381524
import Mathlib

/-!
OEIS A381524: consecutive terms differ by exactly 1.

Write c(n, k) for the absolute coefficient of x^k in H_n; it is positive exactly when k ≤ n and
n - k is even, and for such k with k + 2 ≤ n
  c(n, k + 2) * ((k + 1) (k + 2)) = c(n, k) * (2 (n - k)).
Let k be the least exponent with maximal coefficient. Then n - k is even (the coefficient of x^n
is positive), and 2 (n - k) ≤ (k + 1) (k + 2) (otherwise c(n, k + 2) > c(n, k)), and if k = k' + 2
then (k' + 1) (k' + 2) < 2 (n - k') (otherwise c(n, k') ≥ c(n, k) and k' would be a smaller
maximiser). These conditions for n and for n + 1 force the two exponents to differ by exactly 1:
they have different parities, and a gap of 3 or more contradicts the inequalities.
-/

namespace OMA.A381524

open OMA.S_oeis_a381524

lemma coeff_eq {n k : ℕ} (hk : k ≤ n) (hp : (n - k) % 2 = 0) :
    hermiteAbsCoeff n k = n.factorial / (((n - k) / 2).factorial * k.factorial) * 2 ^ k := by
  unfold hermiteAbsCoeff
  rw [if_pos ⟨hk, hp⟩]

lemma dvd_fact {n k : ℕ} (hk : k ≤ n) :
    ((n - k) / 2).factorial * k.factorial ∣ n.factorial := by
  have h1 : ((n - k) / 2).factorial * k.factorial ∣ ((n - k) / 2 + k).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add _ _
  exact h1.trans (Nat.factorial_dvd_factorial (by omega))

lemma coeff_pos {n k : ℕ} (hk : k ≤ n) (hp : (n - k) % 2 = 0) : 0 < hermiteAbsCoeff n k := by
  rw [coeff_eq hk hp]
  apply Nat.mul_pos
  · exact Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos n) (dvd_fact hk))
      (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  · positivity

lemma key {n k : ℕ} (hk : k + 2 ≤ n) (hp : (n - k) % 2 = 0) :
    hermiteAbsCoeff n (k + 2) * ((k + 1) * (k + 2)) = hermiteAbsCoeff n k * (2 * (n - k)) := by
  have hp' : (n - (k + 2)) % 2 = 0 := by omega
  rw [coeff_eq (by omega) hp, coeff_eq hk hp']
  obtain ⟨j, hj⟩ : ∃ j, n - k = 2 * (j + 1) := ⟨(n - k) / 2 - 1, by omega⟩
  have e1 : (n - k) / 2 = j + 1 := by omega
  have e2 : (n - (k + 2)) / 2 = j := by omega
  have d1 := dvd_fact (n := n) (k := k) (by omega)
  have d2 := dvd_fact (n := n) (k := k + 2) hk
  rw [e1] at d1
  rw [e2] at d2
  rw [e1, e2, hj]
  obtain ⟨B, hB⟩ := d1
  obtain ⟨A, hA⟩ := d2
  have hrel : (j + 1) * B = (k + 2) * (k + 1) * A := by
    have hpos : 0 < j.factorial * k.factorial :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    apply Nat.eq_of_mul_eq_mul_left hpos
    have h := hB.symm.trans hA
    rw [Nat.factorial_succ j, Nat.factorial_succ (k + 1), Nat.factorial_succ k] at h
    linear_combination h
  have hB' : n.factorial / ((j + 1).factorial * k.factorial) = B := by
    rw [hB]
    exact Nat.mul_div_cancel_left B (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  have hA' : n.factorial / (j.factorial * (k + 2).factorial) = A := by
    rw [hA]
    exact Nat.mul_div_cancel_left A (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
  rw [hB', hA', pow_add]
  linear_combination (4 * 2 ^ k) * hrel.symm

lemma lt_step {n k : ℕ} (hk : k + 2 ≤ n) (hp : (n - k) % 2 = 0)
    (hG : (k + 1) * (k + 2) < 2 * (n - k)) :
    hermiteAbsCoeff n k < hermiteAbsCoeff n (k + 2) := by
  have hkey := key hk hp
  have hpos := coeff_pos (n := n) (k := k) (by omega) hp
  by_contra hlt
  push_neg at hlt
  have h1 : hermiteAbsCoeff n (k + 2) * ((k + 1) * (k + 2)) ≤
      hermiteAbsCoeff n k * ((k + 1) * (k + 2)) := Nat.mul_le_mul_right _ hlt
  have h2 : hermiteAbsCoeff n k * ((k + 1) * (k + 2)) < hermiteAbsCoeff n k * (2 * (n - k)) :=
    Nat.mul_lt_mul_of_pos_left hG hpos
  rw [hkey] at h1
  exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)

lemma le_step {n k : ℕ} (hk : k + 2 ≤ n) (hp : (n - k) % 2 = 0)
    (hG : 2 * (n - k) ≤ (k + 1) * (k + 2)) :
    hermiteAbsCoeff n (k + 2) ≤ hermiteAbsCoeff n k := by
  have hkey := key hk hp
  have hX : 0 < (k + 1) * (k + 2) := by positivity
  have h2 : hermiteAbsCoeff n k * (2 * (n - k)) ≤ hermiteAbsCoeff n k * ((k + 1) * (k + 2)) :=
    Nat.mul_le_mul_left _ hG
  rw [← hkey] at h2
  exact Nat.le_of_mul_le_mul_right h2 hX

lemma least_char {n k : ℕ} (h : IsA381524 n k) :
    k ≤ n ∧ (n - k) % 2 = 0 ∧ 2 * (n - k) ≤ (k + 1) * (k + 2) ∧
      ∀ k' : ℕ, k = k' + 2 → (k' + 1) * (k' + 2) < 2 * (n - k') := by
  obtain ⟨⟨hkn, hmax⟩, hleast⟩ := h
  have hpar : (n - k) % 2 = 0 := by
    by_contra hne
    have h0 : hermiteAbsCoeff n k = 0 := by
      unfold hermiteAbsCoeff
      rw [if_neg]
      rintro ⟨-, h⟩
      exact hne h
    have hn := coeff_pos (n := n) (k := n) le_rfl (by simp)
    have hle := hmax n le_rfl
    omega
  have hG : 2 * (n - k) ≤ (k + 1) * (k + 2) := by
    by_contra hnG
    push_neg at hnG
    have hk2 : k + 2 ≤ n := by
      by_contra hc
      have hcases : n - k = 0 ∨ n - k = 1 := by omega
      rcases hcases with h0 | h1
      · rw [h0] at hnG
        simp at hnG
      · omega
    have hlt := lt_step hk2 hpar hnG
    have hle := hmax (k + 2) hk2
    omega
  refine ⟨hkn, hpar, hG, ?_⟩
  rintro k' rfl
  by_contra hcon
  push_neg at hcon
  have hp' : (n - k') % 2 = 0 := by omega
  have hstep := le_step (n := n) (k := k') hkn hp' hcon
  have hmem : k' ∈ {e : ℕ | e ≤ n ∧ ∀ m ≤ n, hermiteAbsCoeff n m ≤ hermiteAbsCoeff n e} :=
    ⟨by omega, fun m hm => (hmax m hm).trans hstep⟩
  have hk := hleast hmem
  omega

end OMA.A381524

open OMA.S_oeis_a381524 OMA.A381524 in
theorem OMA.solution : type_of% @OMA.S_oeis_a381524.main := by
  intro n k₁ k₂ h1 h2
  obtain ⟨a1, p1, g1, l1⟩ := least_char h1
  obtain ⟨a2, p2, g2, l2⟩ := least_char h2
  by_contra hgoal
  push_neg at hgoal
  rcases Nat.lt_or_ge k₁ k₂ with hlt | hge
  · obtain ⟨k', rfl⟩ : ∃ k', k₂ = k' + 2 := ⟨k₂ - 2, by omega⟩
    have hk' : k₁ + 1 ≤ k' := by omega
    have hl := l2 k' rfl
    have hmono : (k₁ + 1) * (k₁ + 2) ≤ k' * (k' + 1) := Nat.mul_le_mul hk' (by omega)
    have hmono2 : k' * (k' + 1) ≤ (k' + 1) * (k' + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega
  · obtain ⟨k', rfl⟩ : ∃ k', k₁ = k' + 2 := ⟨k₁ - 2, by omega⟩
    have hk' : k₂ + 1 ≤ k' := by omega
    have hl := l1 k' rfl
    have hmono : (k₂ + 1) * (k₂ + 2) ≤ k' * (k' + 1) := Nat.mul_le_mul hk' (by omega)
    have hmono2 : k' * (k' + 1) ≤ (k' + 1) * (k' + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega
