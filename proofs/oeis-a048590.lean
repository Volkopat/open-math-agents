import OMAStatements.S_oeis_a048590
import Mathlib.Tactic

/-!
Proof of OEIS A048590 linear recurrence:
Define u(0)=6, u(1)=8, u(2)=11, u(3)=15, u(n+4) = u(n+3) + u(n),
and b(0)=8, b(n+1) = u(n) + 3.
Then Q(n) = u(n)*u(n+2) - u(n+1)^2 satisfies Q(n+6) = Q(n) + Q(n+2) - Q(n+3) - Q(n+4)
and hence Q(n+10) = Q(n+6) + 2*Q(n+5) - 2*Q(n+3) - Q(n+1) + Q(n), giving 4*|Q(n)| <= u(n)
for n >= 7. Combining with b(n)*b(n+2) - b(n+1)^2 = Q(n-1) + 3*u(n-7) for n >= 8 yields
0 <= b(n)*b(n+2) - b(n+1)^2 < b(n) for all n, so a(n) = b(n) for all n.
-/

namespace OMA.P_oeis_a048590

private def u : ℕ → ℕ
  | 0 => 6
  | 1 => 8
  | 2 => 11
  | 3 => 15
  | n + 4 => u (n + 3) + u n

private def b : ℕ → ℕ
  | 0 => 8
  | n + 1 => u n + 3

private lemma u_four (n : ℕ) : u (n + 4) = u (n + 3) + u n := rfl

private lemma u_five (n : ℕ) : u (n + 5) = u (n + 3) + u (n + 1) + u n := by
  change u (n + 4) + u (n + 1) = _
  rw [u_four]
  omega

private lemma u_six (n : ℕ) : u (n + 6) = u (n + 3) + u (n + 2) + u (n + 1) + u n := by
  change u (n + 5) + u (n + 2) = _
  rw [u_five]
  omega

private lemma u_seven (n : ℕ) :
    u (n + 7) = 2 * u (n + 3) + u (n + 2) + u (n + 1) + u n := by
  change u (n + 6) + u (n + 3) = _
  rw [u_six]
  omega

private lemma u_eight (n : ℕ) :
    u (n + 8) = 3 * u (n + 3) + u (n + 2) + u (n + 1) + 2 * u n := by
  change u (n + 7) + u (n + 4) = _
  rw [u_seven, u_four]
  omega

private lemma u_nine (n : ℕ) :
    u (n + 9) = 4 * u (n + 3) + u (n + 2) + 2 * u (n + 1) + 3 * u n := by
  change u (n + 8) + u (n + 5) = _
  rw [u_eight, u_five]
  omega

private lemma u_ten (n : ℕ) :
    u (n + 10) = 5 * u (n + 3) + 2 * u (n + 2) + 3 * u (n + 1) + 4 * u n := by
  change u (n + 9) + u (n + 6) = _
  rw [u_nine, u_six]
  omega

private lemma u_ten_rel (n : ℕ) :
    u (n + 10) + u (n + 1) =
      u (n + 6) + 2 * u (n + 5) + 2 * u (n + 3) + u (n + 2) + u (n + 1) + u n := by
  rw [u_ten, u_six, u_five]
  omega

private lemma u_mono_step (n : ℕ) : u n ≤ u (n + 1) := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | k + 3 =>
    have h : u (k + 4) = u (k + 3) + u k := rfl
    change u (k + 3) ≤ u (k + 4)
    omega

private lemma u_double_le (n : ℕ) : 2 * u n ≤ u (n + 3) := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | k + 4 =>
    have h1 := u_double_le (k + 3)
    have h2 := u_double_le k
    have h4 : u (k + 4) = u (k + 3) + u k := rfl
    have h7 : u (k + 7) = u (k + 6) + u (k + 3) := rfl
    simp only [Nat.add_assoc, Nat.reduceAdd] at h1 h4 h7 ⊢
    omega

private lemma u_two_three (n : ℕ) : 2 * u (n + 1) ≤ 3 * u n := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | k + 3 =>
    have h := u_double_le k
    have h4 : u (k + 4) = u (k + 3) + u k := rfl
    simp only [Nat.add_assoc, Nat.reduceAdd] at h4 ⊢
    omega

private lemma u_four_le_six (m : ℕ) : 4 * u m ≤ u (m + 6) := by
  have h1 := u_double_le m
  have h2 := u_double_le (m + 3)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h2
  omega

private lemma u_six_le_twelve (m : ℕ) : u (m + 6) ≤ 12 * u m := by
  have h01 := u_two_three m
  have h12 := u_two_three (m + 1)
  have h23 := u_two_three (m + 2)
  have h6 := u_six m
  simp only [Nat.add_assoc, Nat.reduceAdd] at h12 h23
  omega

private def Q (n : ℕ) : ℤ := (u n : ℤ) * (u (n + 2) : ℤ) - (u (n + 1) : ℤ) ^ 2

private lemma Q_rec6 (n : ℕ) : Q (n + 6) = Q n + Q (n + 2) - Q (n + 3) - Q (n + 4) := by
  simp only [Q, Nat.add_assoc, Nat.reduceAdd]
  have h4 : (u (n + 4) : ℤ) = (u (n + 3) : ℤ) + (u n : ℤ) := by exact_mod_cast u_four n
  have h5 : (u (n + 5) : ℤ) = (u (n + 3) : ℤ) + (u (n + 1) : ℤ) + (u n : ℤ) := by
    exact_mod_cast u_five n
  have h6 : (u (n + 6) : ℤ) = (u (n + 3) : ℤ) + (u (n + 2) : ℤ) + (u (n + 1) : ℤ) + (u n : ℤ) := by
    exact_mod_cast u_six n
  have h7 : (u (n + 7) : ℤ) = 2 * (u (n + 3) : ℤ) + (u (n + 2) : ℤ) + (u (n + 1) : ℤ) + (u n : ℤ) := by
    exact_mod_cast u_seven n
  have h8 : (u (n + 8) : ℤ) = 3 * (u (n + 3) : ℤ) + (u (n + 2) : ℤ) + (u (n + 1) : ℤ) + 2 * (u n : ℤ) := by
    exact_mod_cast u_eight n
  rw [h8, h7, h6, h5, h4]
  ring

private lemma Q_rec10 (n : ℕ) :
    Q (n + 10) = Q (n + 6) + 2 * Q (n + 5) - 2 * Q (n + 3) - Q (n + 1) + Q n := by
  have h0 := Q_rec6 n
  have h1 := Q_rec6 (n + 1)
  have h2 := Q_rec6 (n + 2)
  have h4 := Q_rec6 (n + 4)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h0 h1 h2 h4
  linarith

private lemma int_abs_le_pair {x y : ℤ} (h : 4 * |x| ≤ y) : -y ≤ 4 * x ∧ 4 * x ≤ y := by
  rcases abs_cases x with ⟨h1, _⟩ | ⟨h1, _⟩ <;> constructor <;> linarith

private lemma int_abs_of_pair {x y : ℤ} (h1 : -y ≤ 4 * x) (h2 : 4 * x ≤ y) : 4 * |x| ≤ y := by
  rcases abs_cases x with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

private lemma Q_bound : ∀ k : ℕ, 4 * |Q (k + 7)| ≤ (u (k + 7) : ℤ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | 5 => decide
    | 6 => decide
    | 7 => decide
    | 8 => decide
    | 9 => decide
    | m + 10 =>
      have hm0 := ih m (by omega)
      have hm1 := ih (m + 1) (by omega)
      have hm3 := ih (m + 3) (by omega)
      have hm5 := ih (m + 5) (by omega)
      have hm6 := ih (m + 6) (by omega)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hm0 hm1 hm3 hm5 hm6 ⊢
      have ⟨p0a, p0b⟩ := int_abs_le_pair hm0
      have ⟨p1a, p1b⟩ := int_abs_le_pair hm1
      have ⟨p3a, p3b⟩ := int_abs_le_pair hm3
      have ⟨p5a, p5b⟩ := int_abs_le_pair hm5
      have ⟨p6a, p6b⟩ := int_abs_le_pair hm6
      have hrec := Q_rec10 (m + 7)
      have hmono := u_mono_step (m + 8)
      have hu : (u (m + 17) : ℤ) + (u (m + 8) : ℤ) =
          (u (m + 13) : ℤ) + 2 * (u (m + 12) : ℤ) + 2 * (u (m + 10) : ℤ) +
            (u (m + 9) : ℤ) + (u (m + 8) : ℤ) + (u (m + 7) : ℤ) := by
        exact_mod_cast u_ten_rel (m + 7)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hrec hmono hu
      apply int_abs_of_pair <;> omega

private def D (n : ℕ) : ℤ := (b n : ℤ) * (b (n + 2) : ℤ) - (b (n + 1) : ℤ) ^ 2

private lemma D_shift (m : ℕ) : D (m + 8) = Q (m + 7) + 3 * (u (m + 1) : ℤ) := by
  simp only [D, Q]
  have hb0 : (b (m + 8) : ℤ) = (u (m + 7) : ℤ) + 3 := rfl
  have hb1 : (b (m + 9) : ℤ) = (u (m + 8) : ℤ) + 3 := rfl
  have hb2 : (b (m + 10) : ℤ) = (u (m + 9) : ℤ) + 3 := rfl
  have hu8 : (u (m + 8) : ℤ) = (u (m + 7) : ℤ) + (u (m + 4) : ℤ) := by
    exact_mod_cast u_four (m + 4)
  have hu9 : (u (m + 9) : ℤ) = (u (m + 8) : ℤ) + (u (m + 5) : ℤ) := by
    exact_mod_cast u_four (m + 5)
  have hu5 : (u (m + 5) : ℤ) = (u (m + 4) : ℤ) + (u (m + 1) : ℤ) := by
    exact_mod_cast u_four (m + 1)
  simp only [Nat.add_assoc, Nat.reduceAdd] at hb0 hb1 hb2 hu8 hu9 hu5 ⊢
  rw [hb0, hb1, hb2]
  linear_combination 3 * hu9 - 3 * hu8 + 3 * hu5

private lemma D_bounds (n : ℕ) : 0 ≤ D n ∧ D n < (b n : ℤ) := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | m + 8 =>
    have hq := Q_bound m
    have hd := D_shift m
    have h4 := u_four_le_six (m + 1)
    have h12 := u_six_le_twelve (m + 1)
    have hb : (b (m + 8) : ℤ) = (u (m + 7) : ℤ) + 3 := rfl
    simp only [Nat.add_assoc, Nat.reduceAdd] at hq hd h4 h12 hb
    have ⟨hqa, hqb⟩ := int_abs_le_pair hq
    omega

private lemma b_pos (n : ℕ) : 0 < b n := by
  match n with
  | 0 => decide
  | k + 1 =>
    have : b (k + 1) = u k + 3 := rfl
    omega

private lemma b_ceil (n : ℕ) : b (n + 2) = ⌈(b (n + 1) : ℚ) ^ 2 / (b n : ℚ)⌉₊ := by
  symm
  have hb2_ne : b (n + 2) ≠ 0 := Nat.ne_of_gt (b_pos (n + 2))
  have hb0_pos : (0 : ℚ) < (b n : ℚ) := Nat.cast_pos.mpr (b_pos n)
  have hb2_pos : 1 ≤ b (n + 2) := b_pos (n + 2)
  rw [Nat.ceil_eq_iff hb2_ne]
  have ⟨hd0, hd1⟩ := D_bounds n
  have hd0q : (0 : ℚ) ≤ (b n : ℚ) * (b (n + 2) : ℚ) - (b (n + 1) : ℚ) ^ 2 := by
    exact_mod_cast hd0
  have hd1q : (b n : ℚ) * (b (n + 2) : ℚ) - (b (n + 1) : ℚ) ^ 2 < (b n : ℚ) := by
    exact_mod_cast hd1
  constructor
  · rw [lt_div_iff₀ hb0_pos, Nat.cast_sub hb2_pos, Nat.cast_one]
    linarith
  · rw [div_le_iff₀ hb0_pos]
    linarith

private lemma a_eq_b : ∀ n : ℕ, OMA.S_oeis_a048590.a n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
      have hk := ih k (by omega)
      have hk1 := ih (k + 1) (by omega)
      change ⌈(OMA.S_oeis_a048590.a (k + 1) : ℚ) ^ 2 / (OMA.S_oeis_a048590.a k : ℚ)⌉₊ = b (k + 2)
      rw [hk, hk1, ← b_ceil]

end OMA.P_oeis_a048590

theorem OMA.solution : type_of% @OMA.S_oeis_a048590.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have h1 := OMA.P_oeis_a048590.a_eq_b (k + 1)
  have h2 := OMA.P_oeis_a048590.a_eq_b (k + 2)
  have h4 := OMA.P_oeis_a048590.a_eq_b (k + 4)
  have h5 := OMA.P_oeis_a048590.a_eq_b (k + 5)
  have h6 := OMA.P_oeis_a048590.a_eq_b (k + 6)
  have hk1 : k + 6 - 1 = k + 5 := by omega
  have hk2 : k + 6 - 2 = k + 4 := by omega
  have hk4 : k + 6 - 4 = k + 2 := by omega
  have hk5 : k + 6 - 5 = k + 1 := by omega
  rw [hk1, hk2, hk4, hk5, h1, h2, h4, h5, h6]
  have hu4 : OMA.P_oeis_a048590.u (k + 4) =
      OMA.P_oeis_a048590.u (k + 3) + OMA.P_oeis_a048590.u k := rfl
  have hu5 : OMA.P_oeis_a048590.u (k + 5) =
      OMA.P_oeis_a048590.u (k + 4) + OMA.P_oeis_a048590.u (k + 1) := rfl
  change ((OMA.P_oeis_a048590.u (k + 5) + 3 : ℕ) : ℤ) =
    2 * ((OMA.P_oeis_a048590.u (k + 4) + 3 : ℕ) : ℤ) -
      ((OMA.P_oeis_a048590.u (k + 3) + 3 : ℕ) : ℤ) +
      ((OMA.P_oeis_a048590.u (k + 1) + 3 : ℕ) : ℤ) -
      ((OMA.P_oeis_a048590.u k + 3 : ℕ) : ℤ)
  omega
