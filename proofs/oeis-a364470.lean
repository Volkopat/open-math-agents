import OMAStatements.S_oeis_a364470

-- Credit: @kumagi

namespace OMA.S_oeis_a364470

private lemma omega_mul {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
    Omega (x * y) = Omega x + Omega y := by
  simpa only [Omega, List.length_append] using
    (Nat.perm_primeFactorsList_mul hx.ne' hy.ne').length_eq

private lemma omega_double {x : ℕ} (hx : 0 < x) : Omega (2 * x) = 1 + Omega x := by
  rw [omega_mul (by decide) hx, show Omega 2 = 1 by simp [Omega, Nat.primeFactorsList_prime Nat.prime_two]]

private lemma three_pow_length_le_prod (l : List ℕ) (h : ∀ p ∈ l, 3 ≤ p) :
    3 ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := h p (by simp)
    have hl := ih (fun q hq => h q (by simp [hq]))
    simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul hp hl

private lemma three_pow_omega_le {k : ℕ} (hk : Odd k) : 3 ^ Omega k ≤ k := by
  have hne : k ≠ 0 := by obtain ⟨m, hm⟩ := hk; omega
  have h : ∀ p ∈ k.primeFactorsList, 3 ≤ p := by
    intro p hp
    by_contra! hsmall
    have ht := (Nat.prime_of_mem_primeFactorsList hp).two_le
    have heq : p = 2 := by omega
    subst p
    have hd := Nat.dvd_of_mem_primeFactorsList hp
    exact (Nat.not_even_iff_odd.mpr hk) (even_iff_two_dvd.mpr hd)
  simpa only [Omega, Nat.prod_primeFactorsList hne] using three_pow_length_le_prod _ h

private def Step (p q n : ℕ) : Prop :=
  p < q ∧ Omega q + Omega (p + q) = n ∧
    ∀ k : Fin q, p < k.val → Omega k.val + Omega (p + k.val) ≠ n

private def Certified (p q n : ℕ) : Prop := Step p q n ∧ q * (p + q) < 3 ^ n

/-- Doubling preserves minimality. Odd candidates have product at least
`3^(n+2)`, while even candidates reduce to the old search interval. -/
private lemma double_certified {p q n : ℕ} (h : Certified p q n) :
    Certified (2 * p) (2 * q) (n + 2) := by
  obtain ⟨⟨hpq, hqn, hmin⟩, hbound⟩ := h
  have hg : (2 * q) * (2 * p + 2 * q) < 3 ^ (n + 2) := by
    rw [pow_add]
    nlinarith
  refine ⟨⟨by omega, ?_, ?_⟩, hg⟩
  · rw [show 2 * p + 2 * q = 2 * (p + q) by ring,
      omega_double (by omega : 0 < q), omega_double (by omega : 0 < p + q)]
    omega
  · rintro ⟨k, hkq⟩ hpk hkn
    change 2 * p < k at hpk
    change Omega k + Omega (2 * p + k) = n + 2 at hkn
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨j, hj⟩ := he
      have hk : k = 2 * j := by omega
      have hpj : p < j := by omega
      have hslow := hmin ⟨j, by omega⟩ hpj
      rw [hk, show 2 * p + 2 * j = 2 * (p + j) by ring,
        omega_double (by omega : 0 < j), omega_double (by omega : 0 < p + j)] at hkn
      exact hslow (by change Omega j + Omega (p + j) = n; omega)
    · have ha : Odd (2 * p + k) := by
        obtain ⟨j, hj⟩ := ho
        exact ⟨p + j, by omega⟩
      have hlow := three_pow_omega_le (ho.mul ha)
      rw [omega_mul (by omega) (by omega), hkn] at hlow
      have hlt : k * (2 * p + k) < (2 * q) * (2 * p + 2 * q) :=
        (Nat.mul_lt_mul_of_pos_right hkq (by omega)).trans_le
          (Nat.mul_le_mul_left _ (by omega))
      exact hlow.not_gt (hlt.trans hg)

private lemma scale {p q n : ℕ} (h : Certified p q n) (t : ℕ) :
    Certified (p * 4 ^ t) (q * 4 ^ t) (n + 4 * t) := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    convert double_certified (double_certified ih) using 1 <;> (try rw [pow_succ]) <;> ring

private lemma next_eq {j q : ℕ} (hj : 1 ≤ j) (h : Step (a j) q (j + 1)) :
    a (j + 1) = q := by
  cases j with
  | zero => omega
  | succ j =>
    let S : Set ℕ := {k | a (j + 1) < k ∧ Omega (k * (a (j + 1) + k)) = j + 2}
    change sInf S = q
    have hq : q ∈ S := by
      refine ⟨h.1, ?_⟩
      rw [omega_mul (by have := h.1; omega) (by have := h.1; omega)]
      exact h.2.1
    have hm := Nat.sInf_mem (show S.Nonempty from ⟨q, hq⟩)
    apply le_antisymm (Nat.sInf_le hq)
    by_contra! hlt
    obtain ⟨hpos, hval⟩ := hm
    rw [omega_mul (by omega) (by omega)] at hval
    exact h.2.2 ⟨sInf S, hlt⟩ hpos hval

set_option maxRecDepth 5000 in
private lemma start_eq : a 7 = 32 := by
  have h₁ : a 1 = 1 := rfl
  have h₂ : a 2 = 2 := next_eq (j := 1) (by decide) (by rw [h₁]; unfold Step; decide +kernel)
  have h₃ : a 3 = 7 := next_eq (j := 2) (by decide) (by rw [h₂]; unfold Step; decide +kernel)
  have h₄ : a 4 = 11 := next_eq (j := 3) (by decide) (by rw [h₃]; unfold Step; decide +kernel)
  have h₅ : a 5 = 13 := next_eq (j := 4) (by decide) (by rw [h₄]; unfold Step; decide +kernel)
  have h₆ : a 6 = 19 := next_eq (j := 5) (by decide) (by rw [h₅]; unfold Step; decide +kernel)
  exact next_eq (j := 6) (by decide) (by rw [h₆]; unfold Step; decide +kernel)

set_option maxRecDepth 7000 in
private lemma seedEight : Certified 32 56 8 := by unfold Certified Step; decide +kernel

set_option maxRecDepth 7000 in
private lemma seedNine : Certified 56 80 9 := by unfold Certified Step; decide +kernel

set_option maxRecDepth 7000 in
private lemma seedTen : Certified 80 120 10 := by unfold Certified Step; decide +kernel

set_option maxRecDepth 7000 in
private lemma seedEleven : Certified 120 128 11 := by unfold Certified Step; decide +kernel

private lemma next_four (t : ℕ) (h₇ : a (4 * t + 7) = 32 * 4 ^ t) :
    a (4 * t + 8) = 56 * 4 ^ t ∧ a (4 * t + 9) = 80 * 4 ^ t ∧
    a (4 * t + 10) = 120 * 4 ^ t ∧ a (4 * t + 11) = 128 * 4 ^ t := by
  have h₈ : a (4 * t + 8) = 56 * 4 ^ t := by
    apply next_eq (j := 4 * t + 7) (by omega)
    rw [h₇, show 4 * t + 7 + 1 = 8 + 4 * t by omega]
    exact (scale seedEight t).1
  have h₉ : a (4 * t + 9) = 80 * 4 ^ t := by
    apply next_eq (j := 4 * t + 8) (by omega)
    rw [h₈, show 4 * t + 8 + 1 = 9 + 4 * t by omega]
    exact (scale seedNine t).1
  have h₁₀ : a (4 * t + 10) = 120 * 4 ^ t := by
    apply next_eq (j := 4 * t + 9) (by omega)
    rw [h₉, show 4 * t + 9 + 1 = 10 + 4 * t by omega]
    exact (scale seedTen t).1
  have h₁₁ : a (4 * t + 11) = 128 * 4 ^ t := by
    apply next_eq (j := 4 * t + 10) (by omega)
    rw [h₁₀, show 4 * t + 10 + 1 = 11 + 4 * t by omega]
    exact (scale seedEleven t).1
  exact ⟨h₈, h₉, h₁₀, h₁₁⟩

private lemma block_start (t : ℕ) : a (4 * t + 7) = 32 * 4 ^ t := by
  induction t with
  | zero => simpa using start_eq
  | succ t ih =>
    rw [show 4 * (t + 1) + 7 = 4 * t + 11 by omega, (next_four t ih).2.2.2,
      pow_succ]
    ring

theorem periodic : ∀ n : ℕ, 7 ≤ n → a (n + 4) = 4 * a n := by
  intro n hn
  let t := (n - 7) / 4
  let r := (n - 7) % 4
  have hr : r < 4 := Nat.mod_lt _ (by decide)
  have hn' : n = 4 * t + 7 + r := by dsimp [t, r]; omega
  obtain ⟨h₈, h₉, h₁₀, _⟩ := next_four t (block_start t)
  obtain ⟨h₁₂, h₁₃, h₁₄, _⟩ := next_four (t + 1) (block_start (t + 1))
  rw [hn']
  interval_cases r
  · rw [show 4 * t + 7 + 0 + 4 = 4 * (t + 1) + 7 by omega, Nat.add_zero,
      block_start, block_start, pow_succ]
    ring
  · rw [show 4 * t + 7 + 1 + 4 = 4 * (t + 1) + 8 by omega,
      show 4 * t + 7 + 1 = 4 * t + 8 by omega, h₁₂, h₈, pow_succ]
    ring
  · rw [show 4 * t + 7 + 2 + 4 = 4 * (t + 1) + 9 by omega,
      show 4 * t + 7 + 2 = 4 * t + 9 by omega, h₁₃, h₉, pow_succ]
    ring
  · rw [show 4 * t + 7 + 3 + 4 = 4 * (t + 1) + 10 by omega,
      show 4 * t + 7 + 3 = 4 * t + 10 by omega, h₁₄, h₁₀, pow_succ]
    ring

end OMA.S_oeis_a364470

theorem OMA.solution : type_of% @OMA.S_oeis_a364470.main :=
  OMA.S_oeis_a364470.periodic
