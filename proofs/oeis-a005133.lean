import OMAStatements.S_oeis_a005133
import Mathlib
-- Credit: @ptc-prover-bot

section
open Finset

namespace A005133Parity

/-- `x` is a power of two. -/
def pw (x : ℕ) : Prop := ∃ k, x = 2 ^ k

lemma pw_odd {x : ℕ} (hx : Odd x) (hp : pw x) : x = 1 := by
  obtain ⟨k, rfl⟩ := hp
  rcases k with _ | k
  · rfl
  · exfalso
    exact (Nat.not_even_iff_odd.mpr hx) (Nat.even_pow.mpr ⟨even_two, by omega⟩)

lemma pw_double {y : ℕ} (hy : 1 ≤ y) : pw (2 * y) ↔ pw y := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · omega
    · exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, rfl⟩; exact ⟨k + 1, by ring⟩

lemma not_pw_pw3 {x : ℕ} (hx : 2 ≤ x) (h1 : pw x) (h2 : pw (x + 3)) : False := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  rcases a with _ | a
  · rw [pow_zero] at ha; omega
  rcases b with _ | b
  · rw [pow_zero] at hb; omega
  rw [pow_succ] at ha hb
  omega

/-- Convolution square of a sequence. -/
def conv (s : ℕ → ℤ) (m : ℕ) : ℤ := ∑ p ∈ antidiagonal m, s p.1 * s p.2

lemma conv_mod_two (s : ℕ → ℤ) (m : ℕ) :
    ((conv s m : ℤ) : ZMod 2) = if Even m then ((s (m / 2) : ℤ) : ZMod 2) else 0 := by
  unfold conv
  push_cast
  set f : ℕ × ℕ → ZMod 2 := fun p => ((s p.1 : ℤ) : ZMod 2) * ((s p.2 : ℤ) : ZMod 2) with hf
  rw [← Finset.sum_filter_add_sum_filter_not (antidiagonal m) (fun p : ℕ × ℕ => p.1 = p.2)]
  have h2 : ∑ p ∈ (antidiagonal m).filter (fun p : ℕ × ℕ => ¬ p.1 = p.2), f p = 0 := by
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p _
      simp only [hf, Prod.fst_swap, Prod.snd_swap]
      rw [mul_comm, ← two_mul]
      exact mul_eq_zero_of_left (by decide) _
    · intro p hp _
      simp only [mem_filter] at hp
      intro h; apply hp.2; have := congrArg Prod.fst h; simpa using this.symm
    · intro p hp
      simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      exact ⟨by omega, fun h => hp.2 h.symm⟩
    · intro p _; simp
  rw [h2, add_zero]
  split_ifs with he
  · obtain ⟨r, rfl⟩ := he
    have : (antidiagonal (r + r)).filter (fun p : ℕ × ℕ => p.1 = p.2) = {(r, r)} := by
      ext ⟨x, y⟩; simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, mem_singleton, Prod.mk.injEq]
      omega
    rw [this, sum_singleton]
    have hr : (r + r) / 2 = r := by omega
    rw [hr]
    show ((s r : ℤ) : ZMod 2) * ((s r : ℤ) : ZMod 2) = ((s r : ℤ) : ZMod 2)
    generalize ((s r : ℤ) : ZMod 2) = t
    fin_cases t <;> rfl
  · have : (antidiagonal m).filter (fun p : ℕ × ℕ => p.1 = p.2) = ∅ := by
      ext ⟨x, y⟩; simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.notMem_empty, iff_false]
      rintro ⟨h1, rfl⟩; exact he ⟨x, by omega⟩
    rw [this, sum_empty]

lemma odd_iff_zmod (z : ℤ) : Odd z ↔ ((z : ℤ) : ZMod 2) = 1 :=
  ZMod.intCast_eq_one_iff_odd.symm

lemma pw_lt (x : ℕ) (hx : x < 32) : pw x ↔ x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8 ∨ x = 16 := by
  constructor
  · rintro ⟨k, rfl⟩
    have hk : k < 5 := by
      by_contra hk
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.mp hk)
      norm_num at this; omega
    interval_cases k <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]

lemma zmod2_xor (x y : ZMod 2) (P Q : Prop) (hx : x = 1 ↔ P) (hy : y = 1 ↔ P ∨ Q)
    (hn : ¬ (P ∧ Q)) : x + y = 1 ↔ Q := by
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  fin_cases x <;> fin_cases y <;> simp [h01, h11] at hx hy ⊢ <;> tauto

/-- **Stothers' parity theorem**, from the Godsil–Imrich–Razen recurrence. -/
theorem odd_iff (s : ℕ → ℤ) (h1 : s 1 = 1) (h2 : s 2 = 1) (h3 : s 3 = 4)
    (h4 : s 4 = 8) (h5 : s 5 = 5) (h6 : s 6 = 22) (h7 : s 7 = 42) (h8 : s 8 = 40)
    (h9 : s 9 = 120)
    (hrec : ∀ n, 10 ≤ n → s n = 4 * s (n - 3) + 2 * s (n - 4) + ((n : ℤ) - 3) * s (n - 6)
      - 2 * s (n - 7) - ((n : ℤ) - 6) * s (n - 9) + conv s (n - 6) - conv s (n - 9)) :
    ∀ n, 1 ≤ n → (Odd (s n) ↔ (pw (n + 3) ∨ pw (n + 6))) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  by_cases hsmall : n < 10
  · interval_cases n <;> simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9] <;>
      rw [Int.odd_iff, pw_lt _ (by norm_num), pw_lt _ (by norm_num)] <;> norm_num
  have hsmall' : 10 ≤ n := by omega
  have e : s n = (((n : ℤ) - 1) * s (n - 6) + (n : ℤ) * s (n - 9) + conv s (n - 6)
      + conv s (n - 9)) + 2 * (2 * s (n - 3) + s (n - 4) - s (n - 6) - s (n - 7)
      - (n : ℤ) * s (n - 9) + 3 * s (n - 9) - conv s (n - 9)) := by
    rw [hrec n hsmall']; ring
  have hmod : ((s n : ℤ) : ZMod 2) = ((n : ZMod 2) - 1) * ((s (n - 6) : ℤ) : ZMod 2)
      + (n : ZMod 2) * ((s (n - 9) : ℤ) : ZMod 2) + ((conv s (n - 6) : ℤ) : ZMod 2)
      + ((conv s (n - 9) : ℤ) : ZMod 2) := by
    rw [e]; push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]
  rw [conv_mod_two, conv_mod_two] at hmod
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2m
    have hn2 : (n : ZMod 2) = 0 := by
      rw [hm, ← two_mul]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul]
    have ev6 : Even (n - 6) := ⟨m - 3, by omega⟩
    have od9 : ¬ Even (n - 9) := by rintro ⟨r, hr⟩; omega
    rw [if_pos ev6, if_neg od9, hn2, show (n - 6) / 2 = m - 3 by omega,
      show ((0 : ZMod 2) - 1) = 1 from rfl] at hmod
    simp only [one_mul, zero_mul, add_zero] at hmod
    have A := ih (n - 6) (by omega) (by omega)
    have B := ih (m - 3) (by omega) (by omega)
    rw [show n - 6 + 3 = 2 * (m - 2) + 1 by omega, show n - 6 + 6 = 2 * m by omega,
      pw_double (y := m) (by omega)] at A
    rw [show m - 3 + 3 = m by omega, show m - 3 + 6 = m + 3 by omega] at B
    have hA : ¬ pw (2 * (m - 2) + 1) := fun hp => by
      have := pw_odd ⟨m - 2, rfl⟩ hp; omega
    rw [show n + 3 = 2 * (m + 1) + 1 by omega, show n + 6 = 2 * (m + 3) by omega,
      pw_double (y := m + 3) (by omega)]
    have hC : ¬ pw (2 * (m + 1) + 1) := fun hp => by
      have := pw_odd ⟨m + 1, rfl⟩ hp; omega
    have hnb : ¬ (pw m ∧ pw (m + 3)) := fun ⟨p, q⟩ => not_pw_pw3 (by omega) p q
    rw [odd_iff_zmod] at A B
    rw [odd_iff_zmod, hmod, or_iff_right hC]
    exact zmod2_xor _ _ _ _ (by rw [A, or_iff_right hA]) B hnb
  · -- n = 2m+1
    have hn2 : (n : ZMod 2) = 1 := by
      rw [hm]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
    have od6 : ¬ Even (n - 6) := by rintro ⟨r, hr⟩; omega
    have ev9 : Even (n - 9) := ⟨m - 4, by omega⟩
    rw [if_neg od6, if_pos ev9, hn2, show (n - 9) / 2 = m - 4 by omega] at hmod
    simp only [sub_self, zero_mul, one_mul, zero_add, add_zero] at hmod
    have A := ih (n - 9) (by omega) (by omega)
    have B := ih (m - 4) (by omega) (by omega)
    rw [show n - 9 + 3 = 2 * (m - 3) + 1 by omega, show n - 9 + 6 = 2 * (m - 1) by omega,
      pw_double (y := m - 1) (by omega)] at A
    rw [show m - 4 + 3 = m - 1 by omega, show m - 4 + 6 = m + 2 by omega] at B
    have hA : ¬ pw (2 * (m - 3) + 1) := fun hp => by
      have := pw_odd ⟨m - 3, rfl⟩ hp; omega
    rw [show n + 3 = 2 * (m + 2) by omega, show n + 6 = 2 * (m + 3) + 1 by omega,
      pw_double (y := m + 2) (by omega)]
    have hC : ¬ pw (2 * (m + 3) + 1) := fun hp => by
      have := pw_odd ⟨m + 3, rfl⟩ hp; omega
    have hnb : ¬ (pw (m - 1) ∧ pw (m + 2)) := fun ⟨p, q⟩ =>
      not_pw_pw3 (x := m - 1) (by omega) p (by rw [show m - 1 + 3 = m + 2 by omega]; exact q)
    rw [odd_iff_zmod] at A B
    rw [odd_iff_zmod, hmod, or_iff_left hC]
    exact zmod2_xor _ _ _ _ (by rw [A, or_iff_right hA]) B hnb

end A005133Parity

end

section
open Finset PowerSeries
open scoped Nat

namespace A005133Series

/-- Convolution square of a sequence. -/
def conv (s : ℕ → ℤ) (m : ℕ) : ℤ := ∑ p ∈ antidiagonal m, s p.1 * s p.2

/-- The linear recurrence for `h n = #Hom(C₂ * C₃, Sₙ)`, as the coefficient of `z^m` of the
differential equation `z⁷(z³-1)H'' + P₁H' + P₀H = 0` for `H = Σ hₙ zⁿ/n!`, times `m!`. -/
def hrecExpr (h : ℕ → ℤ) (m : ℕ) : ℤ :=
  (m.descFactorial 10 : ℤ) * h (m - 10 + 2) - (m.descFactorial 7 : ℤ) * h (m - 7 + 2)
  + 4 * (m.descFactorial 9 : ℤ) * h (m - 9 + 1) + 2 * (m.descFactorial 7 : ℤ) * h (m - 7 + 1)
  - 4 * (m.descFactorial 6 : ℤ) * h (m - 6 + 1) - 2 * (m.descFactorial 4 : ℤ) * h (m - 4 + 1)
  - 4 * (m.descFactorial 3 : ℤ) * h (m - 3 + 1) + (m.descFactorial 0 : ℤ) * h (m - 0 + 1)
  + 2 * (m.descFactorial 8 : ℤ) * h (m - 8 + 0) + 2 * (m.descFactorial 6 : ℤ) * h (m - 6 + 0)
  - 4 * (m.descFactorial 5 : ℤ) * h (m - 5 + 0) + (m.descFactorial 4 : ℤ) * h (m - 4 + 0)
  - 4 * (m.descFactorial 3 : ℤ) * h (m - 3 + 0) - 4 * (m.descFactorial 2 : ℤ) * h (m - 2 + 0)
  - (m.descFactorial 1 : ℤ) * h (m - 1 + 0) - (m.descFactorial 0 : ℤ) * h (m - 0 + 0)

section
variable (h : ℕ → ℤ)

/-- The exponential generating function of `h`. -/
noncomputable def egfH : ℚ⟦X⟧ := mk fun n => (h n : ℚ) / n !

lemma coeff_iter (a j : ℕ) :
    coeff j ((d⁄dX ℚ)^[a] (egfH h)) = (h (j + a) : ℚ) * ((j ! : ℕ) : ℚ)⁻¹ := by
  rw [coeff_iterate_derivative, egfH, coeff_mk]
  have h1 := Nat.factorial_mul_ascFactorial j a
  have h2 : ((j + a) ! : ℚ) = (j ! : ℚ) * ((j + 1).ascFactorial a : ℚ) := by
    rw [← h1]; push_cast; ring
  have h3 : ((j + 1).ascFactorial a : ℚ) ≠ 0 := by
    have := Nat.ascFactorial_pos j a
    exact_mod_cast this.ne'
  have h4 : (j ! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  rw [h2]; field_simp

lemma coeff_term (a b m : ℕ) :
    coeff m (X ^ b * (d⁄dX ℚ)^[a] (egfH h)) =
      ((m.descFactorial b : ℕ) : ℚ) * (h (m - b + a) : ℚ) * ((m ! : ℕ) : ℚ)⁻¹ := by
  rw [coeff_X_pow_mul']
  split_ifs with hb
  · rw [coeff_iter]
    have h1 := Nat.factorial_mul_descFactorial hb
    have h4 : ((m - b) ! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have h5 : (m ! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have h6 : (m ! : ℚ) = ((m - b) ! : ℚ) * (m.descFactorial b : ℚ) := by
      rw [← h1]; push_cast; ring
    rw [show m - b + a = m - b + a from rfl]
    field_simp
    rw [h6]; ring
  · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr (by omega)]; simp

lemma ct2 (b m : ℕ) : coeff m (X ^ b * d⁄dX ℚ (d⁄dX ℚ (egfH h))) =
    ((m.descFactorial b : ℕ) : ℚ) * (h (m - b + 2) : ℚ) * ((m ! : ℕ) : ℚ)⁻¹ :=
  coeff_term h 2 b m

lemma ct1 (b m : ℕ) : coeff m (X ^ b * d⁄dX ℚ (egfH h)) =
    ((m.descFactorial b : ℕ) : ℚ) * (h (m - b + 1) : ℚ) * ((m ! : ℕ) : ℚ)⁻¹ :=
  coeff_term h 1 b m

lemma ct0 (b m : ℕ) : coeff m (X ^ b * egfH h) =
    ((m.descFactorial b : ℕ) : ℚ) * (h (m - b + 0) : ℚ) * ((m ! : ℕ) : ℚ)⁻¹ :=
  coeff_term h 0 b m

/-- The differential equation, from the recurrence. -/
lemma ode (hrec : ∀ m, hrecExpr h m = 0) :
    (X ^ 10 * d⁄dX ℚ (d⁄dX ℚ (egfH h)) - X ^ 7 * d⁄dX ℚ (d⁄dX ℚ (egfH h)))
    + ((4 : ℚ) • (X ^ 9 * d⁄dX ℚ (egfH h)) + (2 : ℚ) • (X ^ 7 * d⁄dX ℚ (egfH h))
      - (4 : ℚ) • (X ^ 6 * d⁄dX ℚ (egfH h)) - (2 : ℚ) • (X ^ 4 * d⁄dX ℚ (egfH h))
      - (4 : ℚ) • (X ^ 3 * d⁄dX ℚ (egfH h)) + X ^ 0 * d⁄dX ℚ (egfH h))
    + ((2 : ℚ) • (X ^ 8 * egfH h) + (2 : ℚ) • (X ^ 6 * egfH h)
      - (4 : ℚ) • (X ^ 5 * egfH h) + X ^ 4 * egfH h
      - (4 : ℚ) • (X ^ 3 * egfH h) - (4 : ℚ) • (X ^ 2 * egfH h)
      - X ^ 1 * egfH h - X ^ 0 * egfH h) = 0 := by
  ext m
  simp only [map_add, map_sub, coeff_smul, smul_eq_mul, ct0, ct1, ct2, map_zero]
  have := congrArg (fun z : ℤ => (z : ℚ) * ((m ! : ℕ) : ℚ)⁻¹) (hrec m)
  simp only [hrecExpr] at this
  push_cast at this ⊢
  linear_combination this

end

/-- **Godsil–Imrich–Razen recurrence** from Hall's relation `z H' = σ H` and the ODE for `H`. -/
theorem gir (h s : ℕ → ℤ) (hh0 : h 0 = 1) (hs0 : s 0 = 0)
    (hrec : ∀ m, hrecExpr h m = 0)
    (hall : ∀ n : ℕ, (n : ℚ) * ((h n : ℚ) / n !) =
      ∑ p ∈ antidiagonal n, (s p.1 : ℚ) * ((h p.2 : ℚ) / p.2 !)) :
    ∀ n, 10 ≤ n → s n = 4 * s (n - 3) + 2 * s (n - 4) + ((n : ℤ) - 3) * s (n - 6)
      - 2 * s (n - 7) - ((n : ℤ) - 6) * s (n - 9) + conv s (n - 6) - conv s (n - 9) := by
  set H := egfH h with hH
  set σ : ℚ⟦X⟧ := mk fun n => (s n : ℚ) with hσ
  have hE := ode h hrec
  simp only [pow_zero, one_mul, smul_eq_C_mul] at hE
  -- Hall: `X * H' = σ * H`
  have hall' : X * d⁄dX ℚ H = σ * H := by
    ext n
    rcases n with _ | n
    · simp [hσ, coeff_mul, hs0]
    · rw [coeff_succ_X_mul, coeff_derivative, coeff_mul, hH, egfH, coeff_mk]
      simp only [hσ, coeff_mk]
      rw [← hall (n + 1)]; push_cast; ring
  -- second derivative
  have hsec : X ^ 2 * d⁄dX ℚ (d⁄dX ℚ H) = (X * d⁄dX ℚ σ + σ ^ 2 - σ) * H := by
    have hd := congrArg (d⁄dX ℚ) hall'
    rw [Derivation.leibniz, Derivation.leibniz, derivative_X] at hd
    simp only [smul_eq_mul] at hd
    linear_combination X * hd + (σ - 1) * hall'
  set T := X * d⁄dX ℚ σ + σ ^ 2 - σ with hT
  -- the Riccati relation
  have hRH : ((X ^ 10 - X ^ 7) * T
      + (C (4 : ℚ) * X ^ 10 + C (2 : ℚ) * X ^ 8 - C (4 : ℚ) * X ^ 7 - C (2 : ℚ) * X ^ 5
        - C (4 : ℚ) * X ^ 4 + X ^ 1) * σ
      + (C (2 : ℚ) * X ^ 10 + C (2 : ℚ) * X ^ 8 - C (4 : ℚ) * X ^ 7 + X ^ 6
        - C (4 : ℚ) * X ^ 5 - C (4 : ℚ) * X ^ 4 - X ^ 3 - X ^ 2)) * H = 0 := by
    linear_combination (X ^ 7 - X ^ 10) * hsec
      - (C (4 : ℚ) * X ^ 10 + C (2 : ℚ) * X ^ 8 - C (4 : ℚ) * X ^ 7 - C (2 : ℚ) * X ^ 5
        - C (4 : ℚ) * X ^ 4 + X) * hall' + X ^ 2 * hE
  have hH0 : H ≠ 0 := by
    intro h0
    have := congrArg (coeff 0) h0
    simp [hH, egfH, hh0] at this
  have hR0 := (mul_eq_zero.mp hRH).resolve_right hH0
  intro n hn
  have hc := congrArg (coeff (n + 1)) hR0
  -- coefficient of `T = X σ' + σ² - σ`
  have cT : ∀ j, 1 ≤ j → coeff j T = (j : ℚ) * s j + (conv s j : ℚ) - s j := by
    intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [hT, map_sub, map_add, coeff_succ_X_mul, coeff_derivative, pow_two, coeff_mul]
    simp only [hσ, coeff_mk, conv]
    push_cast; ring
  have i10 : 10 ≤ n + 1 := by omega
  have i8 : 8 ≤ n + 1 := by omega
  have i7 : 7 ≤ n + 1 := by omega
  have i5 : 5 ≤ n + 1 := by omega
  have i4 : 4 ≤ n + 1 := by omega
  have i1 : 1 ≤ n + 1 := by omega
  have j10 : n + 1 ≠ 10 := by omega
  have j8 : n + 1 ≠ 8 := by omega
  have j7 : n + 1 ≠ 7 := by omega
  have j6 : n + 1 ≠ 6 := by omega
  have j5 : n + 1 ≠ 5 := by omega
  have j4 : n + 1 ≠ 4 := by omega
  have j3 : n + 1 ≠ 3 := by omega
  have j2 : n + 1 ≠ 2 := by omega
  simp only [map_add, map_sub, map_zero, sub_mul, add_mul, mul_assoc, coeff_C_mul,
    coeff_X_pow_mul', coeff_X_pow, i10, i8, i7, i5, i4, i1, j10, j8, j7, j6, j5, j4, j3, j2,
    if_true, if_false, mul_zero, sub_zero, add_zero, mul_one] at hc
  rw [cT (n + 1 - 10) (by omega), cT (n + 1 - 7) (by omega)] at hc
  simp only [hσ, coeff_mk] at hc
  rw [show n + 1 - 10 = n - 9 by omega, show n + 1 - 7 = n - 6 by omega,
    show n + 1 - 8 = n - 7 by omega, show n + 1 - 5 = n - 4 by omega,
    show n + 1 - 4 = n - 3 by omega, show n + 1 - 1 = n by omega] at hc
  have c9 : ((n - 9 : ℕ) : ℚ) = (n : ℚ) - 9 := by rw [Nat.cast_sub (by omega)]; norm_num
  have c6 : ((n - 6 : ℕ) : ℚ) = (n : ℚ) - 6 := by rw [Nat.cast_sub (by omega)]; norm_num
  rw [c9, c6] at hc
  have : (s n : ℚ) = 4 * s (n - 3) + 2 * s (n - 4) + ((n : ℚ) - 3) * s (n - 6)
      - 2 * s (n - 7) - ((n : ℚ) - 6) * s (n - 9) + conv s (n - 6) - conv s (n - 9) := by
    linear_combination hc
  exact_mod_cast this

end A005133Series

end

section
open Finset

namespace A005133HRec

def hrecExpr (h : ℕ → ℤ) (m : ℕ) : ℤ :=
  (m.descFactorial 10 : ℤ) * h (m - 10 + 2) - (m.descFactorial 7 : ℤ) * h (m - 7 + 2)
  + 4 * (m.descFactorial 9 : ℤ) * h (m - 9 + 1) + 2 * (m.descFactorial 7 : ℤ) * h (m - 7 + 1)
  - 4 * (m.descFactorial 6 : ℤ) * h (m - 6 + 1) - 2 * (m.descFactorial 4 : ℤ) * h (m - 4 + 1)
  - 4 * (m.descFactorial 3 : ℤ) * h (m - 3 + 1) + (m.descFactorial 0 : ℤ) * h (m - 0 + 1)
  + 2 * (m.descFactorial 8 : ℤ) * h (m - 8 + 0) + 2 * (m.descFactorial 6 : ℤ) * h (m - 6 + 0)
  - 4 * (m.descFactorial 5 : ℤ) * h (m - 5 + 0) + (m.descFactorial 4 : ℤ) * h (m - 4 + 0)
  - 4 * (m.descFactorial 3 : ℤ) * h (m - 3 + 0) - 4 * (m.descFactorial 2 : ℤ) * h (m - 2 + 0)
  - (m.descFactorial 1 : ℤ) * h (m - 1 + 0) - (m.descFactorial 0 : ℤ) * h (m - 0 + 0)

lemma df (m k : ℕ) : ((m.descFactorial k : ℕ) : ℤ) = ∏ t ∈ range k, ((m : ℤ) - t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, prod_range_succ, ← ih]
    by_cases hk : k ≤ m
    · push_cast [Nat.cast_sub hk]; ring
    · have : m.descFactorial k = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [this]

theorem hrec_of (i c : ℕ → ℤ) (hi0 : i 0 = 1) (hi1 : i 1 = 1)
    (hi : ∀ j : ℕ, i (j + 2) = i (j + 1) + ((j : ℤ) + 1) * i j)
    (hc0 : c 0 = 1) (hc1 : c 1 = 1) (hc2 : c 2 = 1)
    (hc : ∀ j : ℕ, c (j + 3) = c (j + 2) + ((j : ℤ) + 2) * ((j : ℤ) + 1) * c j) :
    ∀ m, hrecExpr (fun j => i j * c j) m = 0 := by
  intro m
  by_cases hm : m < 10
  · have i2 : i 2 = 2 := by rw [hi 0, hi0, hi1]; norm_num
    have i3 : i 3 = 4 := by rw [hi 1, i2, hi1]; norm_num
    have i4 : i 4 = 10 := by rw [hi 2, i3, i2]; norm_num
    have i5 : i 5 = 26 := by rw [hi 3, i4, i3]; norm_num
    have i6 : i 6 = 76 := by rw [hi 4, i5, i4]; norm_num
    have i7 : i 7 = 232 := by rw [hi 5, i6, i5]; norm_num
    have i8 : i 8 = 764 := by rw [hi 6, i7, i6]; norm_num
    have i9 : i 9 = 2620 := by rw [hi 7, i8, i7]; norm_num
    have i10 : i 10 = 9496 := by rw [hi 8, i9, i8]; norm_num
    have c3 : c 3 = 3 := by rw [hc 0, hc2, hc0]; norm_num
    have c4 : c 4 = 9 := by rw [hc 1, c3, hc1]; norm_num
    have c5 : c 5 = 21 := by rw [hc 2, c4, hc2]; norm_num
    have c6 : c 6 = 81 := by rw [hc 3, c5, c3]; norm_num
    have c7 : c 7 = 351 := by rw [hc 4, c6, c4]; norm_num
    have c8 : c 8 = 1233 := by rw [hc 5, c7, c5]; norm_num
    have c9 : c 9 = 5769 := by rw [hc 6, c8, c6]; norm_num
    have c10 : c 10 = 31041 := by rw [hc 7, c9, c7]; norm_num
    interval_cases m <;> simp only [hrecExpr, df, prod_range_succ, prod_range_zero] <;>
      norm_num [hi0, hi1, i2, i3, i4, i5, i6, i7, i8, i9, i10, hc0, hc1, hc2, c3, c4, c5, c6,
        c7, c8, c9, c10]
  obtain ⟨N, rfl⟩ : ∃ N, m = N + 10 := ⟨m - 10, by omega⟩
  simp only [hrecExpr, df, prod_range_succ, prod_range_zero, show N + 10 - 10 + 2 = N + 2 by omega, show N + 10 - 7 + 2 = N + 5 by omega, show N + 10 - 9 + 1 = N + 2 by omega, show N + 10 - 7 + 1 = N + 4 by omega, show N + 10 - 6 + 1 = N + 5 by omega, show N + 10 - 4 + 1 = N + 7 by omega, show N + 10 - 3 + 1 = N + 8 by omega, show N + 10 - 0 + 1 = N + 11 by omega, show N + 10 - 8 + 0 = N + 2 by omega, show N + 10 - 6 + 0 = N + 4 by omega, show N + 10 - 5 + 0 = N + 5 by omega, show N + 10 - 4 + 0 = N + 6 by omega, show N + 10 - 3 + 0 = N + 7 by omega, show N + 10 - 2 + 0 = N + 8 by omega, show N + 10 - 1 + 0 = N + 9 by omega, show N + 10 - 0 + 0 = N + 10 by omega]
  have i11 : i (N + 11) = i (N + 10) + ((N : ℤ) + 10) * i (N + 9) := by
    have := hi (N + 9); rw [show N + 9 + 2 = N + 11 by ring, show N + 9 + 1 = N + 10 by ring] at this; push_cast at this; linear_combination this
  have i10 : i (N + 10) = i (N + 9) + ((N : ℤ) + 9) * i (N + 8) := by
    have := hi (N + 8); rw [show N + 8 + 2 = N + 10 by ring, show N + 8 + 1 = N + 9 by ring] at this; push_cast at this; linear_combination this
  have i9 : i (N + 9) = i (N + 8) + ((N : ℤ) + 8) * i (N + 7) := by
    have := hi (N + 7); rw [show N + 7 + 2 = N + 9 by ring, show N + 7 + 1 = N + 8 by ring] at this; push_cast at this; linear_combination this
  have i8 : i (N + 8) = i (N + 7) + ((N : ℤ) + 7) * i (N + 6) := by
    have := hi (N + 6); rw [show N + 6 + 2 = N + 8 by ring, show N + 6 + 1 = N + 7 by ring] at this; push_cast at this; linear_combination this
  have i7 : i (N + 7) = i (N + 6) + ((N : ℤ) + 6) * i (N + 5) := by
    have := hi (N + 5); rw [show N + 5 + 2 = N + 7 by ring, show N + 5 + 1 = N + 6 by ring] at this; push_cast at this; linear_combination this
  have i6 : i (N + 6) = i (N + 5) + ((N : ℤ) + 5) * i (N + 4) := by
    have := hi (N + 4); rw [show N + 4 + 2 = N + 6 by ring, show N + 4 + 1 = N + 5 by ring] at this; push_cast at this; linear_combination this
  have i5 : i (N + 5) = i (N + 4) + ((N : ℤ) + 4) * i (N + 3) := by
    have := hi (N + 3); rw [show N + 3 + 2 = N + 5 by ring, show N + 3 + 1 = N + 4 by ring] at this; push_cast at this; linear_combination this
  have i4 : i (N + 4) = i (N + 3) + ((N : ℤ) + 3) * i (N + 2) := by
    have := hi (N + 2); rw [show N + 2 + 2 = N + 4 by ring, show N + 2 + 1 = N + 3 by ring] at this; push_cast at this; linear_combination this
  have c11 : c (N + 11) = c (N + 10) + ((N : ℤ) + 10) * ((N : ℤ) + 9) * c (N + 8) := by
    have := hc (N + 8); rw [show N + 8 + 3 = N + 11 by ring, show N + 8 + 2 = N + 10 by ring] at this; push_cast at this; linear_combination this
  have c10 : c (N + 10) = c (N + 9) + ((N : ℤ) + 9) * ((N : ℤ) + 8) * c (N + 7) := by
    have := hc (N + 7); rw [show N + 7 + 3 = N + 10 by ring, show N + 7 + 2 = N + 9 by ring] at this; push_cast at this; linear_combination this
  have c9 : c (N + 9) = c (N + 8) + ((N : ℤ) + 8) * ((N : ℤ) + 7) * c (N + 6) := by
    have := hc (N + 6); rw [show N + 6 + 3 = N + 9 by ring, show N + 6 + 2 = N + 8 by ring] at this; push_cast at this; linear_combination this
  have c8 : c (N + 8) = c (N + 7) + ((N : ℤ) + 7) * ((N : ℤ) + 6) * c (N + 5) := by
    have := hc (N + 5); rw [show N + 5 + 3 = N + 8 by ring, show N + 5 + 2 = N + 7 by ring] at this; push_cast at this; linear_combination this
  have c7 : c (N + 7) = c (N + 6) + ((N : ℤ) + 6) * ((N : ℤ) + 5) * c (N + 4) := by
    have := hc (N + 4); rw [show N + 4 + 3 = N + 7 by ring, show N + 4 + 2 = N + 6 by ring] at this; push_cast at this; linear_combination this
  have c6 : c (N + 6) = c (N + 5) + ((N : ℤ) + 5) * ((N : ℤ) + 4) * c (N + 3) := by
    have := hc (N + 3); rw [show N + 3 + 3 = N + 6 by ring, show N + 3 + 2 = N + 5 by ring] at this; push_cast at this; linear_combination this
  have c5 : c (N + 5) = c (N + 4) + ((N : ℤ) + 4) * ((N : ℤ) + 3) * c (N + 2) := by
    have := hc (N + 2); rw [show N + 2 + 3 = N + 5 by ring, show N + 2 + 2 = N + 4 by ring] at this; push_cast at this; linear_combination this
  simp only [i11, i10, i9, i8, i7, i6, i5, i4, c11, c10, c9, c8, c7, c6, c5]

  push_cast
  ring

end A005133HRec

end

section
open Finset Equiv
open scoped Nat

namespace A005133Counts

/-- The number of permutations of an `n`-set with cycle type `p^k`, as a rational. -/
noncomputable def B (p n k : ℕ) : ℚ :=
  if k * p ≤ n then (n ! : ℚ) / ((n - k * p) ! * (p : ℚ) ^ k * k !) else 0

lemma pow_eq_one_iff {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ} (hp : p.Prime)
    (x : Perm α) : x ^ p = 1 ↔ ∃ k, x.cycleType = Multiset.replicate k p := by
  constructor
  · intro hx
    by_cases h1 : x = 1
    · exact ⟨0, by simp [h1]⟩
    · have hd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hx
      have ho : orderOf x = p := by
        rcases (Nat.dvd_prime hp).mp hd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) h1
        · exact h
      obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (ho ▸ hp)
      exact ⟨n + 1, by rw [hn, ho]⟩
  · rintro ⟨k, hk⟩
    rw [← orderOf_dvd_iff_pow_eq_one, ← Perm.lcm_cycleType, hk]
    exact Multiset.lcm_dvd.mpr fun b hb => by rw [Multiset.eq_of_mem_replicate hb]

lemma card_ct {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((#({x | x.cycleType = Multiset.replicate k p} : Finset (Perm α)) : ℕ) : ℚ) =
      B p (Fintype.card α) k := by
  have h := Perm.card_of_cycleType_mul_eq α (Multiset.replicate k p)
  have hp2 := hp.two_le
  simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.prod_replicate] at h
  have hall : ∀ a ∈ Multiset.replicate k p, 2 ≤ a := fun a ha => by
    rw [Multiset.eq_of_mem_replicate ha]; exact hp2
  have hprod : ∏ n ∈ (Multiset.replicate k p).toFinset, (Multiset.count n (Multiset.replicate k p))!
      = k ! := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Multiset.toFinset_replicate, if_neg hk.ne', prod_singleton, Multiset.count_replicate_self]
  rw [hprod] at h
  unfold B
  by_cases hkp : k * p ≤ Fintype.card α
  · rw [if_pos ⟨hkp, hall⟩] at h
    rw [if_pos hkp, eq_div_iff (by positivity)]
    exact_mod_cast h
  · rw [if_neg (fun hh => hkp hh.1)] at h
    rw [if_neg hkp]
    have : 0 < (Fintype.card α - k * p)! * p ^ k * k ! := by
      have := hp.pos; positivity
    exact_mod_cast (Nat.mul_eq_zero.mp h).resolve_right this.ne'

lemma card_pow_eq_one {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ((#({x | x ^ p = 1} : Finset (Perm (Fin n))) : ℕ) : ℚ) =
      ∑ k ∈ range (n + 1), B p n k := by
  have hsplit : ({x | x ^ p = 1} : Finset (Perm (Fin n))) =
      (range (n + 1)).biUnion fun k => ({x | x.cycleType = Multiset.replicate k p} : Finset _) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
    rw [pow_eq_one_iff hp]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_, hk⟩
      have h1 : x.cycleType.card ≤ x.cycleType.sum := by
        have := Multiset.card_nsmul_le_sum (s := x.cycleType) (a := 1)
          (fun b hb => by have := Perm.two_le_of_mem_cycleType hb; omega)
        simpa using this
      have h2 : x.cycleType.sum ≤ n := by
        rw [Perm.sum_cycleType]; simpa using card_le_univ x.support
      rw [hk, Multiset.card_replicate] at h1
      rw [hk] at h2
      omega
    · rintro ⟨k, _, hk⟩; exact ⟨k, hk⟩
  rw [hsplit, card_biUnion]
  · push_cast
    refine sum_congr rfl fun k _ => ?_
    rw [card_ct hp k, Fintype.card_fin]
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [disjoint_filter]
    intro x _ ha hb
    rw [ha] at hb
    have := congrArg Multiset.card hb
    simp at this
    exact hab this

lemma B_zero (p n : ℕ) : B p n 0 = 1 := by
  unfold B
  rw [if_pos (by omega)]
  simp only [zero_mul, Nat.sub_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
  exact div_self (by positivity)

lemma B_rec (q n k : ℕ) :
    B (q + 1) (n + q + 1) (k + 1) = B (q + 1) (n + q) (k + 1) +
      ((n + q) ! / n ! : ℚ) * B (q + 1) n k := by
  unfold B
  have ht : (k + 1) * (q + 1) = k * (q + 1) + (q + 1) := by ring
  rw [ht]
  by_cases h1 : k * (q + 1) + 1 ≤ n
  · obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 + k * (q + 1) := ⟨n - k * (q + 1) - 1, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    rw [show r + 1 + k * (q + 1) + q + 1 - (k * (q + 1) + (q + 1)) = r + 1 by omega,
      show r + 1 + k * (q + 1) + q - (k * (q + 1) + (q + 1)) = r by omega,
      show r + 1 + k * (q + 1) - k * (q + 1) = r + 1 by omega]
    have F1 : ((r + 1 + k * (q + 1) + q + 1) ! : ℚ) =
        ((r + 1 + k * (q + 1) + q : ℕ) + 1 : ℚ) * ((r + 1 + k * (q + 1) + q) ! : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have F2 : ((r + 1) ! : ℚ) = ((r : ℚ) + 1) * (r ! : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have F3 : ((k + 1) ! : ℚ) = ((k : ℚ) + 1) * (k ! : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [F1, F2, F3]
    have : (r ! : ℚ) ≠ 0 := by positivity
    have : (k ! : ℚ) ≠ 0 := by positivity
    have : ((r + 1 + k * (q + 1) + q) ! : ℚ) ≠ 0 := by positivity
    have : ((r + 1 + k * (q + 1)) ! : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  · by_cases h2 : k * (q + 1) = n
    · subst h2
      rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
      rw [show k * (q + 1) + q + 1 - (k * (q + 1) + (q + 1)) = 0 by omega,
        show k * (q + 1) - k * (q + 1) = 0 by omega]
      have F1 : ((k * (q + 1) + q + 1) ! : ℚ) =
          ((k * (q + 1) + q : ℕ) + 1 : ℚ) * ((k * (q + 1) + q) ! : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have F3 : ((k + 1) ! : ℚ) = ((k : ℚ) + 1) * (k ! : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      rw [F1, F3]
      have : (k ! : ℚ) ≠ 0 := by positivity
      have : ((k * (q + 1) + q) ! : ℚ) ≠ 0 := by positivity
      have : ((k * (q + 1)) ! : ℚ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp

lemma B_eq_zero (p n k : ℕ) (hp : 1 ≤ p) (hk : n < k) : B p n k = 0 := by
  unfold B; rw [if_neg (by nlinarith)]

lemma sum_B_extend (p n M : ℕ) (hp : 1 ≤ p) (hM : n + 1 ≤ M) :
    ∑ k ∈ range (n + 1), B p n k = ∑ k ∈ range M, B p n k := by
  rw [← sum_range_add_sum_Ico _ hM]
  rw [sum_eq_zero (s := Ico (n + 1) M) fun k hk => B_eq_zero p n k hp (by simp at hk; omega)]
  simp

/-- Recurrence for `S(n) = #{x ∈ Sₙ : x^p = 1}`, `p = q + 1`. -/
lemma S_rec (q n : ℕ) :
    ∑ k ∈ range (n + q + 1 + 1), B (q + 1) (n + q + 1) k =
      ∑ k ∈ range (n + q + 1), B (q + 1) (n + q) k +
      ((n + q) ! / n ! : ℚ) * ∑ k ∈ range (n + 1), B (q + 1) n k := by
  rw [sum_B_extend (q + 1) (n + q) (n + q + 2) (by omega) (by omega),
    sum_B_extend (q + 1) n (n + q + 1) (by omega) (by omega)]
  rw [sum_range_succ' _ (n + q + 1), sum_range_succ' _ (n + q + 1), mul_sum]
  simp only [B_rec, sum_add_distrib, B_zero]
  ring

end A005133Counts

end

section
open Matrix Matrix.SpecialLinearGroup
open scoped Pointwise

namespace A005133PSL

abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) ℤ
abbrev PSL2Z := SL2 ⧸ Subgroup.center SL2

/-! ### Cyclic groups as `Multiplicative (ZMod m)` -/

section cyc
variable {K : Type*} [Group K]

/-- The homomorphism `ℤ/m → K` sending the generator to `g` (when `g ^ m = 1`). -/
def cycHom (m : ℕ) (g : K) (hg : g ^ m = 1) : Multiplicative (ZMod m) →* K :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift m ⟨zmultiplesHom (Additive K) (Additive.ofMul g), by
      show ((m : ℤ)) • Additive.ofMul g = 0
      rw [natCast_zsmul, ← ofMul_pow, hg, ofMul_one]⟩)

lemma cycHom_nat (m : ℕ) (g : K) (hg : g ^ m = 1) (k : ℕ) :
    cycHom m g hg (Multiplicative.ofAdd (k : ZMod m)) = g ^ k := by
  have : ((k : ℤ) : ZMod m) = (k : ZMod m) := Int.cast_natCast k
  rw [cycHom, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, Function.comp_apply,
    toAdd_ofAdd, ← this, ZMod.lift_coe]
  simp [ofMul_pow]

lemma ofAdd_nat (m k : ℕ) : Multiplicative.ofAdd (k : ZMod m) =
    (Multiplicative.ofAdd (1 : ZMod m)) ^ k := by
  rw [← ofAdd_nsmul, nsmul_one]

/-- Homomorphisms out of `ℤ/m` are elements of order dividing `m`. -/
def homEquiv (m : ℕ) [NeZero m] :
    (Multiplicative (ZMod m) →* K) ≃ {g : K // g ^ m = 1} where
  toFun φ := ⟨φ (Multiplicative.ofAdd 1), by
    rw [← map_pow, ← ofAdd_nat, ZMod.natCast_self, ofAdd_zero, map_one]⟩
  invFun g := cycHom m g.1 g.2
  left_inv φ := by
    refine MonoidHom.ext fun x => ?_
    show cycHom m _ _ x = φ x
    obtain ⟨y, rfl⟩ : ∃ y : ZMod m, Multiplicative.ofAdd y = x := ⟨Multiplicative.toAdd x, rfl⟩
    rw [← ZMod.natCast_zmod_val y, cycHom_nat, ofAdd_nat m y.val, map_pow]
  right_inv g := by
    apply Subtype.ext
    show cycHom m g.1 g.2 (Multiplicative.ofAdd 1) = g.1
    rw [← Nat.cast_one, cycHom_nat, pow_one]

end cyc

/-! ### Generators of `PSL₂(ℤ)` -/

def U : SL2 := ⟨!![1, -1; 1, 0], by simp [Matrix.det_fin_two_of]⟩
def U2 : SL2 := ⟨!![0, -1; 1, -1], by simp [Matrix.det_fin_two_of]⟩

lemma coe_U : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 1, 0] := rfl
lemma coe_U2 : (U2 : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, -1] := rfl

lemma U_mul_U : U * U = U2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [coe_U, coe_U2, coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma U2_mul_U : U2 * U = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [coe_U, coe_U2, coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma S_mul_S : ModularGroup.S * ModularGroup.S = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_S, coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma T_mul_S : ModularGroup.T * ModularGroup.S = U := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [coe_U, ModularGroup.coe_S, ModularGroup.coe_T, coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

lemma neg_one_mem : (-1 : SL2) ∈ Subgroup.center SL2 :=
  Subgroup.mem_center_iff.mpr fun g => by simp

def sbar : PSL2Z := ((ModularGroup.S : SL2) : PSL2Z)
def ubar : PSL2Z := ((U : SL2) : PSL2Z)

lemma sbar_sq : sbar ^ 2 = 1 := by
  rw [sbar, ← QuotientGroup.mk_pow, pow_two, S_mul_S, QuotientGroup.eq_one_iff]
  exact neg_one_mem

lemma ubar_sq : ubar ^ 2 = ((U2 : SL2) : PSL2Z) := by
  rw [ubar, ← QuotientGroup.mk_pow, pow_two, U_mul_U]

lemma ubar_cube : ubar ^ 3 = 1 := by
  rw [ubar, ← QuotientGroup.mk_pow, pow_succ, pow_two, U_mul_U, U2_mul_U, QuotientGroup.eq_one_iff]
  exact neg_one_mem

/-! ### The free product `C₂ * C₃` -/

abbrev M : Fin 2 → ℕ := ![2, 3]
abbrev H (i : Fin 2) : Type := Multiplicative (ZMod (M i))

instance (i : Fin 2) : NeZero (M i) := ⟨by fin_cases i <;> decide⟩

def gen : Fin 2 → PSL2Z := ![sbar, ubar]

lemma gen_pow (i : Fin 2) : gen i ^ M i = 1 := by
  fin_cases i
  · exact sbar_sq
  · exact ubar_cube

def f (i : Fin 2) : H i →* PSL2Z := cycHom (M i) (gen i) (gen_pow i)

def φ : Monoid.CoprodI H →* PSL2Z := Monoid.CoprodI.lift f

lemma f0 : f 0 (Multiplicative.ofAdd ((1 : ℕ) : ZMod (M 0))) = sbar := by
  show cycHom (M 0) (gen 0) (gen_pow 0) _ = sbar
  rw [cycHom_nat, pow_one]; rfl

lemma f1 : f 1 (Multiplicative.ofAdd ((1 : ℕ) : ZMod (M 1))) = ubar := by
  show cycHom (M 1) (gen 1) (gen_pow 1) _ = ubar
  rw [cycHom_nat, pow_one]; rfl

lemma f1' : f 1 (Multiplicative.ofAdd ((2 : ℕ) : ZMod (M 1))) = ubar ^ 2 := by
  show cycHom (M 1) (gen 1) (gen_pow 1) _ = ubar ^ 2
  rw [cycHom_nat]; rfl

lemma φ_surjective : Function.Surjective φ := by
  have hs : sbar ∈ φ.range :=
    ⟨Monoid.CoprodI.of (i := 0) (Multiplicative.ofAdd ((1 : ℕ) : ZMod (M 0))), by
      rw [φ, Monoid.CoprodI.lift_of, f0]⟩
  have hu : ubar ∈ φ.range :=
    ⟨Monoid.CoprodI.of (i := 1) (Multiplicative.ofAdd ((1 : ℕ) : ZMod (M 1))), by
      rw [φ, Monoid.CoprodI.lift_of, f1]⟩
  have key : (⊤ : Subgroup SL2) ≤ φ.range.comap (QuotientGroup.mk' (Subgroup.center SL2)) := by
    rw [← SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hs
    · show ((ModularGroup.T : SL2) : PSL2Z) ∈ φ.range
      have hT : ModularGroup.T = U * ModularGroup.S⁻¹ := by
        rw [← T_mul_S, mul_inv_cancel_right]
      rw [hT, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact φ.range.mul_mem hu (φ.range.inv_mem hs)
  intro g
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective g
  exact key (Subgroup.mem_top A)

/-! ### Ping-pong on the projective line -/

/-- `SL₂(ℤ)` acting on `ℝ ∪ {∞}` by Möbius transformations. -/
noncomputable def ρ : SL2 →* Equiv.Perm (OnePoint ℝ) :=
  (MulAction.toPermHom (GL (Fin 2) ℝ) (OnePoint ℝ)).comp
    (SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map (Int.castRingHom ℝ)))

lemma ρ_apply (A : SL2) (x : OnePoint ℝ) :
    ρ A x = (SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) A)) • x := rfl

lemma toGL_entry (A : SL2) (i j : Fin 2) :
    ((SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) A) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) i j = (A i j : ℝ) := rfl

lemma ρ_some (A : SL2) (x : ℝ) : ρ A (x : OnePoint ℝ) =
    if (A 1 0 : ℝ) * x + A 1 1 = 0 then (OnePoint.infty : OnePoint ℝ) else
      (((A 0 0 : ℝ) * x + A 0 1) / ((A 1 0 : ℝ) * x + A 1 1) : ℝ) := by
  rw [ρ_apply, OnePoint.smul_some_eq_ite]
  rfl

lemma center_le_ker : Subgroup.center SL2 ≤ ρ.ker := by
  intro A hA
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [MonoidHom.mem_ker]
  have hr' : r = 1 ∨ r = -1 := by
    simp only [Fintype.card_fin] at hr
    have : (r - 1) * (r + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  have hr0 : (r : ℝ) ≠ 0 := by rcases hr' with rfl | rfl <;> norm_num
  have e : ∀ i j, A i j = (scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) ℤ) i j := fun i j => by
    rw [hA']
  have a10 : A 1 0 = 0 := by rw [e, Matrix.scalar_apply, Matrix.diagonal_apply]; simp
  have a01 : A 0 1 = 0 := by rw [e, Matrix.scalar_apply, Matrix.diagonal_apply]; simp
  have a00 : A 0 0 = r := by rw [e, Matrix.scalar_apply, Matrix.diagonal_apply]; simp
  have a11 : A 1 1 = r := by rw [e, Matrix.scalar_apply, Matrix.diagonal_apply]; simp
  ext x
  rw [Equiv.Perm.one_apply]
  cases x with
  | infty =>
    rw [ρ_apply, OnePoint.smul_infty_eq_ite, toGL_entry, a10]
    simp
  | coe x =>
    rw [ρ_some, a10, a11, a00, a01]
    simp [hr0]

noncomputable def ρbar : PSL2Z →* Equiv.Perm (OnePoint ℝ) :=
  QuotientGroup.lift _ ρ center_le_ker

noncomputable instance : MulAction PSL2Z (OnePoint ℝ) := MulAction.compHom _ ρbar

lemma smul_mk (A : SL2) (x : OnePoint ℝ) : ((A : PSL2Z) • x) = ρ A x := rfl

lemma sbar_act (x : ℝ) (hx : 0 < x) : sbar • (x : OnePoint ℝ) = ((-1 / x : ℝ) : OnePoint ℝ) := by
  rw [sbar, smul_mk, ρ_some]
  simp [ModularGroup.coe_S, hx.ne']

lemma ubar_act (x : ℝ) (hx : x < 0) : ubar • (x : OnePoint ℝ) = (((x - 1) / x : ℝ) : OnePoint ℝ) := by
  rw [ubar, smul_mk, ρ_some]
  simp [coe_U, hx.ne, sub_eq_add_neg]

lemma ubar2_act (x : ℝ) (hx : x < 0) :
    (ubar ^ 2) • (x : OnePoint ℝ) = ((-1 / (x - 1) : ℝ) : OnePoint ℝ) := by
  have hx1 : x + -1 ≠ 0 := by intro h; linarith
  rw [ubar_sq, smul_mk, ρ_some]
  simp [coe_U2, sub_eq_add_neg, hx1]

def X : Fin 2 → Set (OnePoint ℝ) :=
  ![(fun x : ℝ => (x : OnePoint ℝ)) '' Set.Iio 0, (fun x : ℝ => (x : OnePoint ℝ)) '' Set.Ioi 0]

lemma C2_ne (h : H 0) (hh : h ≠ 1) :
    h = Multiplicative.ofAdd ((1 : ℕ) : ZMod (M 0)) := by
  revert h; decide

lemma C3_ne (h : H 1) (hh : h ≠ 1) :
    h = Multiplicative.ofAdd ((1 : ℕ) : ZMod (M 1)) ∨
      h = Multiplicative.ofAdd ((2 : ℕ) : ZMod (M 1)) := by
  revert h; decide

lemma φ_injective : Function.Injective φ := by
  have hcard : 3 ≤ Cardinal.mk (Fin 2) ∨ ∃ i, 3 ≤ Cardinal.mk (H i) := by
    refine Or.inr ⟨1, ?_⟩
    show (3 : Cardinal) ≤ Cardinal.mk (Multiplicative (ZMod 3))
    rw [Cardinal.mk_fintype]
    have : Fintype.card (Multiplicative (ZMod 3)) = 3 := by simp
    rw [this]; norm_num
  have hne : ∀ i, (X i).Nonempty := by
    intro i; fin_cases i
    · exact ⟨((-1 : ℝ) : OnePoint ℝ), -1, by norm_num, rfl⟩
    · exact ⟨((1 : ℝ) : OnePoint ℝ), 1, by norm_num, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint X) := by
    have key : Disjoint (X 0) (X 1) := by
      rw [Set.disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have := OnePoint.coe_injective hab
      simp only [Set.mem_Iio, Set.mem_Ioi] at ha hb
      linarith
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact key
    · exact key.symm
    · exact absurd rfl hij
  have hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • X j ⊆ X i := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · intro h hh
      show f 0 h • X 1 ⊆ X 0
      rw [C2_ne h hh, f0]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      simp only [Set.mem_Ioi] at hx
      show sbar • (x : OnePoint ℝ) ∈ (fun x : ℝ => (x : OnePoint ℝ)) '' Set.Iio 0
      rw [sbar_act x hx]
      exact ⟨-1 / x, div_neg_of_neg_of_pos (by norm_num) hx, rfl⟩
    · intro h hh
      show f 1 h • X 0 ⊆ X 1
      rcases C3_ne h hh with e | e
      · rw [e, f1]
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        simp only [Set.mem_Iio] at hx
        show ubar • (x : OnePoint ℝ) ∈ (fun x : ℝ => (x : OnePoint ℝ)) '' Set.Ioi 0
        rw [ubar_act x hx]
        exact ⟨(x - 1) / x, div_pos_of_neg_of_neg (by linarith) hx, rfl⟩
      · rw [e, f1']
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        simp only [Set.mem_Iio] at hx
        show (ubar ^ 2) • (x : OnePoint ℝ) ∈ (fun x : ℝ => (x : OnePoint ℝ)) '' Set.Ioi 0
        rw [ubar2_act x hx]
        exact ⟨-1 / (x - 1), show (0 : ℝ) < -1 / (x - 1) from
          div_pos_of_neg_of_neg (by norm_num) (by linarith), rfl⟩
    · exact absurd rfl hij
  exact Monoid.CoprodI.lift_injective_of_ping_pong (f := f) (hcard := hcard) (X := X)
    (hXnonempty := hne) (hXdisj := hdisj) (hpp := hpp)

/-- `PSL₂(ℤ) ≅ C₂ * C₃`. -/
noncomputable def iso : Monoid.CoprodI H ≃* PSL2Z :=
  MulEquiv.ofBijective φ ⟨φ_injective, φ_surjective⟩

/-- Precomposition with the isomorphism. -/
noncomputable def precomp (K : Type*) [Group K] : (PSL2Z →* K) ≃ (Monoid.CoprodI H →* K) where
  toFun ψ := ψ.comp iso.toMonoidHom
  invFun χ := χ.comp iso.symm.toMonoidHom
  left_inv ψ := by ext g; simp
  right_inv χ := by ext g; simp

/-- Homomorphisms out of `PSL₂(ℤ)`: pairs `(x, y)` with `x² = 1`, `y³ = 1`. -/
noncomputable def homEquivPSL (K : Type*) [Group K] :
    (PSL2Z →* K) ≃ {x : K // x ^ 2 = 1} × {y : K // y ^ 3 = 1} :=
  (((precomp K).trans Monoid.CoprodI.lift.symm).trans
    (Equiv.piCongrRight fun i => homEquiv (M i))).trans
    (piFinTwoEquiv fun i => {g : K // g ^ M i = 1})

theorem card_hom (n : ℕ) :
    Nat.card (PSL2Z →* Equiv.Perm (Fin n)) =
      (Finset.univ.filter fun x : Equiv.Perm (Fin n) => x ^ 2 = 1).card *
      (Finset.univ.filter fun x : Equiv.Perm (Fin n) => x ^ 3 = 1).card := by
  rw [Nat.card_congr (homEquivPSL _), Nat.card_prod, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]

instance finiteHom (n : ℕ) : Finite (PSL2Z →* Equiv.Perm (Fin n)) :=
  Finite.of_equiv _ (homEquivPSL _).symm

end A005133PSL

end

section
open Finset Equiv
open scoped Nat

namespace A005133Hall

variable {G : Type*} [Group G]

/-- A transitive permutation representation. -/
def IsTrans {α : Type*} (ψ : G →* Perm α) : Prop := ∀ x y, ∃ g, ψ g x = y

/-- Conjugation by a bijection, as a homomorphism of permutation groups. -/
def conjHom {α β : Type*} (e : α ≃ β) : Perm α →* Perm β where
  toFun σ := e.permCongr σ
  map_one' := by ext x; simp [Equiv.permCongr_apply]
  map_mul' σ τ := by ext x; simp [Equiv.permCongr_apply, Perm.mul_apply]

lemma conjHom_apply {α β : Type*} (e : α ≃ β) (σ : Perm α) (x : β) :
    conjHom e σ x = e (σ (e.symm x)) := rfl

/-- Transport of permutation representations along a bijection. -/
def homCongr {α β : Type*} (e : α ≃ β) : (G →* Perm α) ≃ (G →* Perm β) where
  toFun ψ := (conjHom e).comp ψ
  invFun χ := (conjHom e.symm).comp χ
  left_inv ψ := by ext g x; simp [conjHom_apply]
  right_inv χ := by ext g x; simp [conjHom_apply]

lemma homCongr_apply {α β : Type*} (e : α ≃ β) (ψ : G →* Perm α) (g : G) (x : β) :
    homCongr e ψ g x = e (ψ g (e.symm x)) := rfl

lemma isTrans_homCongr {α β : Type*} (e : α ≃ β) (ψ : G →* Perm α) :
    IsTrans (homCongr e ψ) ↔ IsTrans ψ := by
  constructor
  · intro h x y
    obtain ⟨g, hg⟩ := h (e x) (e y)
    refine ⟨g, ?_⟩
    rw [homCongr_apply, symm_apply_apply] at hg
    exact e.injective hg
  · intro h x y
    obtain ⟨g, hg⟩ := h (e.symm x) (e.symm y)
    exact ⟨g, by rw [homCongr_apply, hg, apply_symm_apply]⟩

def transCongr {α β : Type*} (e : α ≃ β) :
    {ψ : G →* Perm α // IsTrans ψ} ≃ {χ : G →* Perm β // IsTrans χ} :=
  (homCongr e).subtypeEquiv fun ψ => (isTrans_homCongr e ψ).symm

/-- `Nat.card` as a sum over the fibres of a map to a finite type. -/
lemma card_eq_sum_fibers {α β : Type*} [Finite α] [Fintype β] (f : α → β) :
    Nat.card α = ∑ y, Nat.card {x // f x = y} := by
  classical
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, ← Fintype.card_congr (Equiv.sigmaFiberEquiv f),
    Fintype.card_sigma]
  refine sum_congr rfl fun y _ => ?_
  rw [Nat.card_eq_fintype_card]

/-! ### Transitive actions and subgroups of finite index -/

/-- Stabilizer of a point. -/
def stab {α : Type*} (ψ : G →* Perm α) (y : α) : Subgroup G :=
  (MulAction.stabilizer (Perm α) y).comap ψ

lemma mem_stab {α : Type*} (ψ : G →* Perm α) (y : α) (g : G) : g ∈ stab ψ y ↔ ψ g y = y := by
  simp [stab, MulAction.mem_stabilizer_iff, Perm.smul_def]

section fiber
variable {m : ℕ} (H : Subgroup G)

/-- The orbit map `G ⧸ Stab(y) → Fin m`, `gH ↦ g • y`. -/
def orbitMap (ψ : G →* Perm (Fin m)) (y : Fin m) (hp : stab ψ y = H) : G ⧸ H → Fin m :=
  Quotient.lift (fun g => ψ g y) (by
    intro a b hab
    have h1 : a⁻¹ * b ∈ H := QuotientGroup.eq.mp (Quotient.sound hab)
    rw [← hp, mem_stab, map_mul, Perm.mul_apply, map_inv, Perm.inv_def,
      Equiv.symm_apply_eq] at h1
    exact h1.symm)

lemma orbitMap_mk (ψ : G →* Perm (Fin m)) (y : Fin m) (hp : stab ψ y = H) (g : G) :
    orbitMap H ψ y hp (g : G ⧸ H) = ψ g y := rfl

lemma orbitMap_bij (ψ : G →* Perm (Fin m)) (ht : IsTrans ψ) (y : Fin m) (hp : stab ψ y = H) :
    Function.Bijective (orbitMap H ψ y hp) := by
  constructor
  · intro u v huv
    induction u using QuotientGroup.induction_on with | H a => ?_
    induction v using QuotientGroup.induction_on with | H b => ?_
    rw [orbitMap_mk, orbitMap_mk] at huv
    apply QuotientGroup.eq.mpr
    rw [← hp, mem_stab, map_mul, Perm.mul_apply, ← huv, map_inv, Perm.inv_def,
      Equiv.symm_apply_apply]
  · intro z
    obtain ⟨g, hg⟩ := ht y z
    exact ⟨(g : G ⧸ H), hg⟩

/-- The permutation representation on `Fin m` coming from `e : G ⧸ H ≃ Fin m`. -/
def repOf (e : G ⧸ H ≃ Fin m) : G →* Perm (Fin m) :=
  (conjHom e).comp (MulAction.toPermHom G (G ⧸ H))

lemma repOf_apply (e : G ⧸ H ≃ Fin m) (g : G) (x : Fin m) :
    repOf H e g x = e (g • e.symm x) := rfl

lemma repOf_trans (e : G ⧸ H ≃ Fin m) : IsTrans (repOf H e) := by
  intro x y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (e.symm x) (e.symm y)
  exact ⟨g, by rw [repOf_apply, hg, apply_symm_apply]⟩

lemma repOf_stab (e : G ⧸ H ≃ Fin m) : stab (repOf H e) (e ((1 : G) : G ⧸ H)) = H := by
  ext g
  rw [mem_stab, repOf_apply, symm_apply_apply, e.apply_eq_iff_eq, MulAction.Quotient.smul_mk,
    smul_eq_mul, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]

/-- Fibre of the stabilizer map over `H`. -/
noncomputable def fiberEquiv :
    {p : {ψ : G →* Perm (Fin m) // IsTrans ψ} × Fin m // stab p.1.1 p.2 = H} ≃
      (G ⧸ H ≃ Fin m) where
  toFun p := Equiv.ofBijective _ (orbitMap_bij H p.1.1.1 p.1.1.2 p.1.2 p.2)
  invFun e := ⟨(⟨repOf H e, repOf_trans H e⟩, e ((1 : G) : G ⧸ H)), repOf_stab H e⟩
  left_inv p := by
    obtain ⟨⟨⟨ψ, ht⟩, y⟩, hp⟩ := p
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      refine MonoidHom.ext fun g => Equiv.ext fun x => ?_
      show (Equiv.ofBijective _ (orbitMap_bij H ψ ht y hp))
        (g • (Equiv.ofBijective _ (orbitMap_bij H ψ ht y hp)).symm x) = ψ g x
      obtain ⟨u, rfl⟩ := (Equiv.ofBijective _ (orbitMap_bij H ψ ht y hp)).surjective x
      rw [symm_apply_apply]
      induction u using QuotientGroup.induction_on with | H a => ?_
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]
      show orbitMap H ψ y hp ((g * a : G) : G ⧸ H) = ψ g (orbitMap H ψ y hp (a : G ⧸ H))
      rw [orbitMap_mk, orbitMap_mk, map_mul, Perm.mul_apply]
    · show orbitMap H ψ y hp ((1 : G) : G ⧸ H) = y
      rw [orbitMap_mk, map_one, Perm.one_apply]
  right_inv e := by
    refine Equiv.ext fun u => ?_
    induction u using QuotientGroup.induction_on with | H a => ?_
    show orbitMap H (repOf H e) (e ((1 : G) : G ⧸ H)) (repOf_stab H e) (a : G ⧸ H) = e (a : G ⧸ H)
    rw [orbitMap_mk, repOf_apply, symm_apply_apply, MulAction.Quotient.smul_mk, smul_eq_mul,
      mul_one]

end fiber

lemma card_equiv_fin {α : Type*} {m : ℕ} (hm : 0 < m) (h : Nat.card α = m) :
    Nat.card (α ≃ Fin m) = m ! := by
  haveI : Finite α := Nat.finite_of_card_ne_zero (by omega)
  have e0 : α ≃ Fin m := (Finite.equivFin α).trans (finCongr h)
  rw [Nat.card_congr (e0.equivCongr (Equiv.refl (Fin m))), Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]

/-! ### Counting transitive representations -/

theorem card_trans (m : ℕ) (hm : 0 < m) [Finite (G →* Perm (Fin m))] :
    Nat.card {ψ : G →* Perm (Fin m) // IsTrans ψ} * m =
      Nat.card {H : Subgroup G // H.index = m} * m ! := by
  classical
  have hP : Nat.card ({ψ : G →* Perm (Fin m) // IsTrans ψ} × Fin m) =
      Nat.card {ψ : G →* Perm (Fin m) // IsTrans ψ} * m := by
    rw [Nat.card_prod, Nat.card_fin]
  have hidx : ∀ p : {ψ : G →* Perm (Fin m) // IsTrans ψ} × Fin m,
      (stab p.1.1 p.2).index = m := fun p => by
    rw [Subgroup.index_eq_card,
      Nat.card_congr (Equiv.ofBijective _ (orbitMap_bij _ p.1.1 p.1.2 p.2 rfl)), Nat.card_fin]
  let π : {ψ : G →* Perm (Fin m) // IsTrans ψ} × Fin m → {H : Subgroup G // H.index = m} :=
    fun p => ⟨stab p.1.1 p.2, hidx p⟩
  have hsurj : Function.Surjective π := by
    rintro ⟨H, hH⟩
    have hc : Nat.card (G ⧸ H) = m := by rw [← Subgroup.index_eq_card, hH]
    haveI : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero (by omega)
    let e : G ⧸ H ≃ Fin m := (Finite.equivFin _).trans (finCongr hc)
    exact ⟨((fiberEquiv H).symm e).1, Subtype.ext ((fiberEquiv H).symm e).2⟩
  haveI : Finite {H : Subgroup G // H.index = m} := Finite.of_surjective π hsurj
  haveI := Fintype.ofFinite {H : Subgroup G // H.index = m}
  rw [← hP, card_eq_sum_fibers π]
  have hfib : ∀ y, Nat.card {p // π p = y} = m ! := by
    rintro ⟨H, hH⟩
    have e1 : {p // π p = ⟨H, hH⟩} ≃
        {p : {ψ : G →* Perm (Fin m) // IsTrans ψ} × Fin m // stab p.1.1 p.2 = H} :=
      Equiv.subtypeEquivRight fun p => by simp [π, Subtype.ext_iff]
    rw [Nat.card_congr (e1.trans (fiberEquiv H)),
      card_equiv_fin hm (by rw [← Subgroup.index_eq_card, hH])]
  rw [sum_congr rfl fun y _ => hfib y, sum_const, card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card]

/-! ### Orbit decomposition -/

section orbit
variable {n : ℕ}

open scoped Classical in
/-- The orbit of `0`. -/
noncomputable def orb (ph : G →* Perm (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  univ.filter fun x => ∃ g, ph g 0 = x

lemma mem_orb (ph : G →* Perm (Fin (n + 1))) (x : Fin (n + 1)) :
    x ∈ orb ph ↔ ∃ g, ph g 0 = x := by
  simp [orb]

lemma orb_inv (ph : G →* Perm (Fin (n + 1))) (g : G) (x : Fin (n + 1)) :
    ph g x ∈ orb ph ↔ x ∈ orb ph := by
  rw [mem_orb, mem_orb]
  constructor
  · rintro ⟨g', hg'⟩
    refine ⟨g⁻¹ * g', ?_⟩
    rw [map_mul, Perm.mul_apply, hg', map_inv, Perm.inv_def, symm_apply_apply]
  · rintro ⟨g', hg'⟩
    exact ⟨g * g', by rw [map_mul, Perm.mul_apply, hg']⟩

lemma zero_mem_orb (ph : G →* Perm (Fin (n + 1))) : 0 ∈ orb ph :=
  (mem_orb ph 0).mpr ⟨1, by rw [map_one, Perm.one_apply]⟩

/-- Restriction to an invariant subset. -/
def restr {α : Type*} (ph : G →* Perm α) (p : α → Prop) (hp : ∀ g x, p (ph g x) ↔ p x) :
    G →* Perm {x // p x} where
  toFun g := (ph g).subtypePerm (hp g)
  map_one' := by
    refine Equiv.ext fun x => Subtype.ext ?_
    show ph 1 (x : α) = x
    rw [map_one, Perm.one_apply]
  map_mul' g h := by
    refine Equiv.ext fun x => Subtype.ext ?_
    show ph (g * h) (x : α) = ph g (ph h x)
    rw [map_mul, Perm.mul_apply]

lemma restr_apply {α : Type*} (ph : G →* Perm α) (p : α → Prop) (hp : ∀ g x, p (ph g x) ↔ p x)
    (g : G) (x : {x // p x}) : ((restr ph p hp g x : {x // p x}) : α) = ph g x := rfl

/-- Gluing two representations. -/
def glue {α : Type*} (p : α → Prop) [DecidablePred p] (ψ : G →* Perm {x // p x})
    (χ : G →* Perm {x // ¬ p x}) : G →* Perm α :=
  (Perm.subtypeCongrHom p).comp (ψ.prod χ)

lemma glue_pos {α : Type*} (p : α → Prop) [DecidablePred p] (ψ : G →* Perm {x // p x})
    (χ : G →* Perm {x // ¬ p x}) (g : G) {x : α} (hx : p x) : glue p ψ χ g x = ψ g ⟨x, hx⟩ :=
  Perm.subtypeCongr.left_apply (ψ g) (χ g) hx

lemma glue_neg {α : Type*} (p : α → Prop) [DecidablePred p] (ψ : G →* Perm {x // p x})
    (χ : G →* Perm {x // ¬ p x}) (g : G) {x : α} (hx : ¬ p x) : glue p ψ χ g x = χ g ⟨x, hx⟩ :=
  Perm.subtypeCongr.right_apply (ψ g) (χ g) hx

lemma restr_trans (ph : G →* Perm (Fin (n + 1))) (A : Finset (Fin (n + 1))) (hph : orb ph = A)
    (hp : ∀ g x, ph g x ∈ A ↔ x ∈ A) : IsTrans (restr ph (· ∈ A) hp) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [← hph, mem_orb] at hx hy
  obtain ⟨g1, rfl⟩ := hx
  obtain ⟨g2, rfl⟩ := hy
  refine ⟨g2 * g1⁻¹, Subtype.ext ?_⟩
  rw [restr_apply, map_mul, Perm.mul_apply, map_inv, Perm.inv_def, symm_apply_apply]

/-- Splitting a representation along the orbit of `0`. -/
noncomputable def orbEquiv (A : Finset (Fin (n + 1))) (hA : 0 ∈ A) :
    {ph : G →* Perm (Fin (n + 1)) // orb ph = A} ≃
      {ψ : G →* Perm {x // x ∈ A} // IsTrans ψ} × (G →* Perm {x // x ∉ A}) where
  toFun ph :=
    (⟨restr ph.1 (· ∈ A) (fun g x => by have h := orb_inv ph.1 g x; rwa [ph.2] at h),
      restr_trans ph.1 A ph.2 _⟩,
     restr ph.1 (· ∉ A) (fun g x => by have h := not_congr (orb_inv ph.1 g x); rwa [ph.2] at h))
  invFun q := ⟨glue (· ∈ A) q.1.1 q.2, by
    ext x
    rw [mem_orb]
    constructor
    · rintro ⟨g, rfl⟩
      rw [glue_pos _ _ _ g hA]
      exact (q.1.1 g ⟨0, hA⟩).2
    · intro hx
      obtain ⟨g, hg⟩ := q.1.2 ⟨0, hA⟩ ⟨x, hx⟩
      exact ⟨g, by rw [glue_pos _ _ _ g hA, hg]⟩⟩
  left_inv ph := by
    apply Subtype.ext
    refine MonoidHom.ext fun g => Equiv.ext fun x => ?_
    by_cases hx : x ∈ A
    · rw [glue_pos _ _ _ g hx]; rfl
    · rw [glue_neg _ _ _ g hx]; rfl
  right_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      refine MonoidHom.ext fun g => Equiv.ext fun x => Subtype.ext ?_
      show glue (· ∈ A) q.1.1 q.2 g x = _
      rw [glue_pos _ _ _ g x.2]
    · refine MonoidHom.ext fun g => Equiv.ext fun x => Subtype.ext ?_
      show glue (· ∈ A) q.1.1 q.2 g x = _
      rw [glue_neg _ _ _ g x.2]

lemma card_compl_sub (A : Finset (Fin (n + 1))) :
    Fintype.card {x // x ∉ A} = n + 1 - A.card := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => (mem_compl (s := A) (a := x)).symm)),
    Fintype.card_coe, card_compl, Fintype.card_fin]

lemma card_fiber_orb (A : Finset (Fin (n + 1))) (hA : 0 ∈ A) :
    Nat.card {ph : G →* Perm (Fin (n + 1)) // orb ph = A} =
      Nat.card {ψ : G →* Perm (Fin A.card) // IsTrans ψ} *
        Nat.card (G →* Perm (Fin (n + 1 - A.card))) := by
  rw [Nat.card_congr (orbEquiv A hA), Nat.card_prod, Nat.card_congr (transCongr A.equivFin),
    Nat.card_congr (homCongr (Fintype.equivFinOfCardEq (card_compl_sub A)))]

lemma card_sets (k : ℕ) :
    ((univ.filter fun A : Finset (Fin (n + 1)) => 0 ∈ A).filter fun A => A.card = k + 1).card =
      n.choose k := by
  have hc : (powersetCard k (univ.erase (0 : Fin (n + 1)))).card = n.choose k := by
    rw [card_powersetCard, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
      Nat.add_sub_cancel]
  rw [← hc]
  apply card_nbij' (fun A => A.erase 0) (fun B => insert 0 B)
  · intro A hA
    simp only [mem_coe, mem_filter, mem_univ, true_and, mem_powersetCard] at hA ⊢
    exact ⟨erase_subset_erase _ (subset_univ _), by rw [card_erase_of_mem hA.1, hA.2]; rfl⟩
  · intro B hB
    simp only [mem_coe, mem_filter, mem_univ, true_and, mem_powersetCard] at hB ⊢
    have h0 : (0 : Fin (n + 1)) ∉ B := fun h => by simpa using hB.1 h
    exact ⟨mem_insert_self _ _, by rw [card_insert_of_notMem h0, hB.2]⟩
  · intro A hA
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hA
    exact insert_erase hA.1
  · intro B hB
    simp only [mem_coe, mem_powersetCard] at hB
    have h0 : (0 : Fin (n + 1)) ∉ B := fun h => by simpa using hB.1 h
    exact erase_insert h0

/-- **Hall's formula** in counting form. -/
theorem hall_sum (n : ℕ) [hf : ∀ m, Finite (G →* Perm (Fin m))] :
    Nat.card (G →* Perm (Fin (n + 1))) = ∑ k ∈ range (n + 1), n.choose k *
      (Nat.card {ψ : G →* Perm (Fin (k + 1)) // IsTrans ψ} *
        Nat.card (G →* Perm (Fin (n - k)))) := by
  classical
  rw [card_eq_sum_fibers (orb (G := G) (n := n))]
  set F : ℕ → ℕ := fun j => Nat.card {ψ : G →* Perm (Fin j) // IsTrans ψ} *
    Nat.card (G →* Perm (Fin (n + 1 - j))) with hF
  have h1 : ∀ A : Finset (Fin (n + 1)),
      Nat.card {ph : G →* Perm (Fin (n + 1)) // orb ph = A} = if 0 ∈ A then F A.card else 0 := by
    intro A
    split_ifs with hA
    · exact card_fiber_orb A hA
    · rw [Nat.card_eq_zero]
      left
      exact ⟨fun ⟨ph, hph⟩ => hA (hph ▸ zero_mem_orb ph)⟩
  rw [sum_congr rfl fun A _ => h1 A, ← sum_filter]
  rw [← sum_fiberwise_of_maps_to (g := Finset.card) (t := range (n + 2)) (fun A _ => by
    rw [mem_range]; have := card_le_univ A; rw [Fintype.card_fin] at this; omega)]
  have h2 : ∀ j ∈ range (n + 2),
      ∑ A ∈ (univ.filter fun A : Finset (Fin (n + 1)) => 0 ∈ A) with A.card = j, F A.card =
      ((univ.filter fun A : Finset (Fin (n + 1)) => 0 ∈ A).filter (fun A => A.card = j)).card *
        F j := by
    intro j _
    rw [sum_congr rfl fun A hA => by rw [(mem_filter.mp hA).2], sum_const, smul_eq_mul]
  rw [sum_congr rfl h2, sum_range_succ']
  have h0 : ((univ.filter fun A : Finset (Fin (n + 1)) => 0 ∈ A).filter
      (fun A => A.card = 0)).card = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro A hA h
    rw [card_eq_zero] at h
    subst h
    simp at hA
  rw [h0, zero_mul, add_zero]
  refine sum_congr rfl fun k _ => ?_
  rw [card_sets, hF]
  simp only
  rw [show n + 1 - (k + 1) = n - k by omega]

end orbit

end A005133Hall

end

namespace A005133Final

open Finset Equiv
open scoped Nat

abbrev G := OMA.S_oeis_a005133.PSL2Z

noncomputable def hN (n : ℕ) : ℕ := Nat.card (G →* Perm (Fin n))
def I (n : ℕ) : ℕ := (univ.filter fun x : Perm (Fin n) => x ^ 2 = 1).card
def C3 (n : ℕ) : ℕ := (univ.filter fun x : Perm (Fin n) => x ^ 3 = 1).card

instance finHom (n : ℕ) : Finite (G →* Perm (Fin n)) := A005133PSL.finiteHom n

lemma hN_eq (n : ℕ) : hN n = I n * C3 n := A005133PSL.card_hom n

lemma I_rec (n : ℕ) : (I (n + 2) : ℤ) = I (n + 1) + ((n : ℤ) + 1) * I n := by
  have h := A005133Counts.S_rec 1 n
  have hf : ((n + 1)! / n ! : ℚ) = n + 1 := by
    rw [Nat.factorial_succ]; push_cast
    have : (n ! : ℚ) ≠ 0 := by positivity
    field_simp
  rw [hf] at h
  have a := A005133Counts.card_pow_eq_one Nat.prime_two (n + 2)
  have b := A005133Counts.card_pow_eq_one Nat.prime_two (n + 1)
  have c := A005133Counts.card_pow_eq_one Nat.prime_two n
  have : (I (n + 2) : ℚ) = I (n + 1) + ((n : ℚ) + 1) * I n := by
    rw [I, I, I, a, b, c]; exact h
  exact_mod_cast this

lemma C3_rec (n : ℕ) :
    (C3 (n + 3) : ℤ) = C3 (n + 2) + ((n : ℤ) + 2) * ((n : ℤ) + 1) * C3 n := by
  have h := A005133Counts.S_rec 2 n
  have hf : ((n + 2)! / n ! : ℚ) = (n + 2) * (n + 1) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast
    have : (n ! : ℚ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hf] at h
  have a := A005133Counts.card_pow_eq_one Nat.prime_three (n + 3)
  have b := A005133Counts.card_pow_eq_one Nat.prime_three (n + 2)
  have c := A005133Counts.card_pow_eq_one Nat.prime_three n
  have : (C3 (n + 3) : ℚ) = C3 (n + 2) + ((n : ℚ) + 2) * ((n : ℚ) + 1) * C3 n := by
    rw [C3, C3, C3, a, b, c]
    exact h
  exact_mod_cast this

lemma I0 : I 0 = 1 := by
  have := A005133Counts.card_pow_eq_one Nat.prime_two 0
  rw [← I] at this
  norm_num [Finset.sum_range_succ, A005133Counts.B] at this
  exact_mod_cast this

lemma I1 : I 1 = 1 := by
  have := A005133Counts.card_pow_eq_one Nat.prime_two 1
  rw [← I] at this
  norm_num [Finset.sum_range_succ, A005133Counts.B] at this
  exact_mod_cast this

lemma C0 : C3 0 = 1 := by
  have := A005133Counts.card_pow_eq_one Nat.prime_three 0
  rw [← C3] at this
  norm_num [Finset.sum_range_succ, A005133Counts.B] at this
  exact_mod_cast this

lemma C1 : C3 1 = 1 := by
  have := A005133Counts.card_pow_eq_one Nat.prime_three 1
  rw [← C3] at this
  norm_num [Finset.sum_range_succ, A005133Counts.B] at this
  exact_mod_cast this

lemma C2 : C3 2 = 1 := by
  have := A005133Counts.card_pow_eq_one Nat.prime_three 2
  rw [← C3] at this
  norm_num [Finset.sum_range_succ, A005133Counts.B] at this
  exact_mod_cast this

/-- The subgroup counts, with `s 0 = 0`. -/
noncomputable def s (n : ℕ) : ℤ := if n = 0 then 0 else (OMA.S_oeis_a005133.a n : ℤ)

lemma s_zero : s 0 = 0 := by simp [s]

lemma s_pos (n : ℕ) (hn : n ≠ 0) : s n = OMA.S_oeis_a005133.a n := by simp [s, hn]

lemma trans_eq (k : ℕ) :
    (Nat.card {ψ : G →* Perm (Fin (k + 1)) // A005133Hall.IsTrans ψ} : ℚ) =
      (OMA.S_oeis_a005133.a (k + 1) : ℚ) * k ! := by
  have h := A005133Hall.card_trans (G := G) (k + 1) (by omega)
  have h' : (Nat.card {ψ : G →* Perm (Fin (k + 1)) // A005133Hall.IsTrans ψ} : ℚ) * (k + 1) =
      (Nat.card {H : Subgroup G // H.index = k + 1} : ℚ) * ((k + 1) * k !) := by
    have h2 := h
    rw [Nat.factorial_succ] at h2
    exact_mod_cast h2
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have e : (OMA.S_oeis_a005133.a (k + 1) : ℚ) =
      (Nat.card {H : Subgroup G // H.index = k + 1} : ℚ) := rfl
  rw [e]
  apply mul_right_cancel₀ hk
  linear_combination h'

lemma hall_q (n : ℕ) : (n : ℚ) * (((hN n : ℤ) : ℚ) / n !) =
    ∑ p ∈ antidiagonal n, (s p.1 : ℚ) * (((hN p.2 : ℤ) : ℚ) / p.2 !) := by
  rcases n with _ | n
  · simp [s_zero]
  rw [Finset.Nat.sum_antidiagonal_succ, s_zero, Int.cast_zero, zero_mul, zero_add,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hs := A005133Hall.hall_sum (G := G) n
  have hn : (n ! : ℚ) ≠ 0 := by positivity
  have lhs : ((n + 1 : ℕ) : ℚ) * (((hN (n + 1) : ℤ) : ℚ) / (n + 1)!) = (hN (n + 1) : ℚ) / n ! := by
    rw [Nat.factorial_succ]; push_cast
    have : ((n : ℚ) + 1) ≠ 0 := by positivity
    field_simp
  rw [lhs, hN, hs]
  push_cast
  rw [Finset.sum_div]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := by rw [mem_range] at hk; omega
  rw [trans_eq, s_pos (k + 1) (by omega)]
  have hc : (n.choose k : ℚ) * k ! * (n - k)! = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hf : ((n - k)! : ℚ) ≠ 0 := by positivity
  rw [div_eq_iff hn, ← hc]
  push_cast
  have hd : (Nat.card (G →* Perm (Fin (n - k))) : ℚ) / ((n - k)! : ℚ) * ((n - k)! : ℚ) =
      Nat.card (G →* Perm (Fin (n - k))) := div_mul_cancel₀ _ hf
  simp only [hN]
  linear_combination (-(OMA.S_oeis_a005133.a (k + 1) : ℚ) * (n.choose k) * k !) * hd

theorem gir_s : ∀ n, 10 ≤ n → s n = 4 * s (n - 3) + 2 * s (n - 4) + ((n : ℤ) - 3) * s (n - 6)
      - 2 * s (n - 7) - ((n : ℤ) - 6) * s (n - 9) + A005133Series.conv s (n - 6)
      - A005133Series.conv s (n - 9) := by
  have hh0 : ((hN 0 : ℕ) : ℤ) = 1 := by rw [hN_eq, I0, C0]; rfl
  have hrec : ∀ m, A005133Series.hrecExpr (fun j => (hN j : ℤ)) m = 0 := by
    have := A005133HRec.hrec_of (fun j => (I j : ℤ)) (fun j => (C3 j : ℤ))
      (by simp [I0]) (by simp [I1]) I_rec (by simp [C0]) (by simp [C1]) (by simp [C2]) C3_rec
    intro m
    have e : (fun j => (hN j : ℤ)) = fun j => (I j : ℤ) * (C3 j : ℤ) := by
      funext j; rw [hN_eq]; push_cast; rfl
    rw [e]
    exact this m
  exact A005133Series.gir (fun j => (hN j : ℤ)) s hh0 s_zero hrec hall_q

/-- Small values of `a`. -/
lemma small_values : s 1 = 1 ∧ s 2 = 1 ∧ s 3 = 4 ∧ s 4 = 8 ∧ s 5 = 5 ∧ s 6 = 22 ∧ s 7 = 42 ∧
    s 8 = 40 ∧ s 9 = 120 := by
  have i2 : (I 2 : ℤ) = 2 := by rw [I_rec 0, I1, I0]; norm_num
  have i3 : (I 3 : ℤ) = 4 := by rw [I_rec 1, i2, I1]; norm_num
  have i4 : (I 4 : ℤ) = 10 := by rw [I_rec 2, i3, i2]; norm_num
  have i5 : (I 5 : ℤ) = 26 := by rw [I_rec 3, i4, i3]; norm_num
  have i6 : (I 6 : ℤ) = 76 := by rw [I_rec 4, i5, i4]; norm_num
  have i7 : (I 7 : ℤ) = 232 := by rw [I_rec 5, i6, i5]; norm_num
  have i8 : (I 8 : ℤ) = 764 := by rw [I_rec 6, i7, i6]; norm_num
  have i9 : (I 9 : ℤ) = 2620 := by rw [I_rec 7, i8, i7]; norm_num
  have c3 : (C3 3 : ℤ) = 3 := by rw [C3_rec 0, C2, C0]; norm_num
  have c4 : (C3 4 : ℤ) = 9 := by rw [C3_rec 1, c3, C1]; norm_num
  have c5 : (C3 5 : ℤ) = 21 := by rw [C3_rec 2, c4, C2]; norm_num
  have c6 : (C3 6 : ℤ) = 81 := by rw [C3_rec 3, c5, c3]; norm_num
  have c7 : (C3 7 : ℤ) = 351 := by rw [C3_rec 4, c6, c4]; norm_num
  have c8 : (C3 8 : ℤ) = 1233 := by rw [C3_rec 5, c7, c5]; norm_num
  have c9 : (C3 9 : ℤ) = 5769 := by rw [C3_rec 6, c8, c6]; norm_num
  have hv : ∀ j, ((hN j : ℤ) : ℚ) = ((I j : ℤ) : ℚ) * ((C3 j : ℤ) : ℚ) := by
    intro j; rw [hN_eq]; push_cast; ring
  have h0 : ((hN 0 : ℤ) : ℚ) = 1 := by rw [hv]; simp [I0, C0]
  have h1 : ((hN 1 : ℤ) : ℚ) = 1 := by rw [hv]; simp [I1, C1]
  have h2 : ((hN 2 : ℤ) : ℚ) = 2 := by rw [hv, i2]; simp [C2]
  have h3 : ((hN 3 : ℤ) : ℚ) = 12 := by rw [hv, i3, c3]; norm_num
  have h4 : ((hN 4 : ℤ) : ℚ) = 90 := by rw [hv, i4, c4]; norm_num
  have h5 : ((hN 5 : ℤ) : ℚ) = 546 := by rw [hv, i5, c5]; norm_num
  have h6 : ((hN 6 : ℤ) : ℚ) = 6156 := by rw [hv, i6, c6]; norm_num
  have h7 : ((hN 7 : ℤ) : ℚ) = 81432 := by rw [hv, i7, c7]; norm_num
  have h8 : ((hN 8 : ℤ) : ℚ) = 942012 := by rw [hv, i8, c8]; norm_num
  have h9 : ((hN 9 : ℤ) : ℚ) = 15114780 := by rw [hv, i9, c9]; norm_num
  have E : ∀ n : ℕ, (n : ℚ) * (((hN n : ℤ) : ℚ) / n !) =
      ∑ k ∈ range (n + 1), (s k : ℚ) * (((hN (n - k) : ℤ) : ℚ) / (n - k)!) := by
    intro n; rw [hall_q, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have e1 := E 1
  have e2 := E 2
  have e3 := E 3
  have e4 := E 4
  have e5 := E 5
  have e6 := E 6
  have e7 := E 7
  have e8 := E 8
  have e9 := E 9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, s_zero, Nat.factorial,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9] at e1 e2 e3 e4 e5 e6 e7 e8 e9
  norm_num [Nat.factorial] at e1 e2 e3 e4 e5 e6 e7 e8 e9
  have q1 : (s 1 : ℚ) = 1 := by linarith
  have q2 : (s 2 : ℚ) = 1 := by linarith
  have q3 : (s 3 : ℚ) = 4 := by linarith
  have q4 : (s 4 : ℚ) = 8 := by linarith
  have q5 : (s 5 : ℚ) = 5 := by linarith
  have q6 : (s 6 : ℚ) = 22 := by linarith
  have q7 : (s 7 : ℚ) = 42 := by linarith
  have q8 : (s 8 : ℚ) = 40 := by linarith
  have q9 : (s 9 : ℚ) = 120 := by linarith
  exact ⟨by exact_mod_cast q1, by exact_mod_cast q2, by exact_mod_cast q3, by exact_mod_cast q4,
    by exact_mod_cast q5, by exact_mod_cast q6, by exact_mod_cast q7, by exact_mod_cast q8,
    by exact_mod_cast q9⟩

theorem stothers : ∀ n, 1 ≤ n →
    (Odd (s n) ↔ (A005133Parity.pw (n + 3) ∨ A005133Parity.pw (n + 6))) := by
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := small_values
  exact A005133Parity.odd_iff s v1 v2 v3 v4 v5 v6 v7 v8 v9 gir_s

lemma odd_a_iff (n : ℕ) (hn : 1 ≤ n) :
    Odd (OMA.S_oeis_a005133.a n) ↔ (A005133Parity.pw (n + 3) ∨ A005133Parity.pw (n + 6)) := by
  rw [← stothers n hn, s_pos n (by omega), Int.odd_coe_nat]

theorem main' :
    (∀ n : ℕ, 1 ≤ n → Odd n →
      (OMA.S_oeis_a005133.a n % 2 = OMA.S_oeis_a005133.a (2 * n) % 2)) ∧
    (∀ n : ℕ, 1 ≤ n → Even (OMA.S_oeis_a005133.a (4 * n))) := by
  constructor
  · intro n hn hodd
    obtain ⟨m, rfl⟩ := hodd
    have A := odd_a_iff (2 * m + 1) hn
    have B := odd_a_iff (2 * (2 * m + 1)) (by omega)
    have n6 : ¬ A005133Parity.pw (2 * m + 1 + 6) := fun h => by
      have := A005133Parity.pw_odd ⟨m + 3, by ring⟩ h; omega
    have n3 : ¬ A005133Parity.pw (2 * (2 * m + 1) + 3) := fun h => by
      have := A005133Parity.pw_odd ⟨2 * m + 2, by ring⟩ h; omega
    rw [or_iff_left n6] at A
    rw [or_iff_right n3, show 2 * (2 * m + 1) + 6 = 2 * (2 * m + 1 + 3) by ring,
      A005133Parity.pw_double (y := 2 * m + 1 + 3) (by omega)] at B
    have key : Odd (OMA.S_oeis_a005133.a (2 * m + 1)) ↔
        Odd (OMA.S_oeis_a005133.a (2 * (2 * m + 1))) := by rw [A, B]
    rcases Nat.even_or_odd (OMA.S_oeis_a005133.a (2 * m + 1)) with h | h
    · have h' : ¬ Odd (OMA.S_oeis_a005133.a (2 * (2 * m + 1))) := fun h2 =>
        (Nat.not_odd_iff_even.mpr h) (key.mpr h2)
      rw [Nat.not_odd_iff_even] at h'
      rw [Nat.even_iff.mp h, Nat.even_iff.mp h']
    · rw [Nat.odd_iff.mp h, Nat.odd_iff.mp (key.mp h)]
  · intro n hn
    have A := odd_a_iff (4 * n) (by omega)
    have n3 : ¬ A005133Parity.pw (4 * n + 3) := fun h => by
      have := A005133Parity.pw_odd ⟨2 * n + 1, by ring⟩ h; omega
    have n6 : ¬ A005133Parity.pw (4 * n + 6) := fun h => by
      rw [show 4 * n + 6 = 2 * (2 * n + 3) by ring,
        A005133Parity.pw_double (y := 2 * n + 3) (by omega)] at h
      have := A005133Parity.pw_odd ⟨n + 1, by ring⟩ h; omega
    rw [← Nat.not_odd_iff_even, A]
    tauto

end A005133Final

theorem OMA.solution : type_of% @OMA.S_oeis_a005133.main := A005133Final.main'


