import OMAStatements.S_oeis_a026389
import Mathlib

-- Credit: @hermitokatt (Lean proof with Claude Code)

/-!
Proof of R. J. Mathar's recurrence for A026389.

1. With the generalized trinomial coefficients `U L d` (the coefficient of `y^d` in
   `(y⁻¹ + 3 + y)^L`), the rows of the array `T` of A026386 are, by induction on `m`,
   `T(2m+1, k) = U(m, k-m) + U(m, k-m-1)` and `T(2m+2, k) = U(m+1, k-m-1) - U(m, k-m-1)`
   (the boundary entries come from `U(m, ±m) = 1` and `U(m, d) = 0` for `|d| > m`).
2. Hence `a(l+1) = T(2l+2, l-1) = U(l,1) + 2 U(l,2) + U(l,3)` for `l ≥ 1`.
3. The row relation `(L+d+1) U(L,d+1) + 3d U(L,d) - (L-d+1) U(L,d-1) = 0` expresses all values
   through `U(m,0)` and `U(m,1)`; the recurrence, multiplied by a positive polynomial `D(m)`, is
   an explicit linear combination of these relations (checked by `linear_combination`).
-/

namespace OMA.A026389Proof

open OMA.S_oeis_a026389

/-- Generalized trinomial coefficients: `U L d` is the coefficient of `y^d` in `(y⁻¹ + 3 + y)^L`. -/
def U : ℕ → ℤ → ℤ
  | 0, d => if d = 0 then 1 else 0
  | L + 1, d => U L (d - 1) + 3 * U L d + U L (d + 1)

theorem U_zero (d : ℤ) : U 0 d = if d = 0 then 1 else 0 := rfl

theorem U_succ (L : ℕ) (d : ℤ) : U (L + 1) d = U L (d - 1) + 3 * U L d + U L (d + 1) := rfl

theorem U_succ' (L : ℕ) (d a b : ℤ) (ha : a = d - 1) (hb : b = d + 1) :
    U (L + 1) d = U L a + 3 * U L d + U L b := by
  subst ha hb; exact U_succ L d

theorem U_symm (L : ℕ) : ∀ d, U L (-d) = U L d := by
  induction L with
  | zero => intro d; simp [U_zero]
  | succ L ih =>
    intro d
    rw [U_succ, U_succ, show -d - 1 = -(d + 1) by ring, show -d + 1 = -(d - 1) by ring, ih, ih, ih]
    ring

theorem U_symm' (L : ℕ) (d e : ℤ) (h : e = -d) : U L e = U L d := by rw [h, U_symm]

/-- The row relation `(L+d+1) U(L,d+1) + 3d U(L,d) - (L-d+1) U(L,d-1) = 0`. -/
theorem U_rel (L : ℕ) : ∀ d : ℤ,
    ((L : ℤ) + d + 1) * U L (d + 1) + 3 * d * U L d - ((L : ℤ) - d + 1) * U L (d - 1) = 0 := by
  induction L with
  | zero =>
    intro d
    simp only [U_zero]
    split_ifs <;> omega
  | succ L ih =>
    intro d
    have h1 := ih (d + 1)
    have h0 := ih d
    have hm := ih (d - 1)
    rw [U_succ' L (d + 1) d (d + 2) (by ring) (by ring), U_succ' L d (d - 1) (d + 1) rfl rfl,
      U_succ' L (d - 1) (d - 2) d (by ring) (by ring)]
    rw [show d + 1 + 1 = d + 2 by ring, show d + 1 - 1 = d by ring] at h1
    rw [show d - 1 + 1 = d by ring, show d - 1 - 1 = d - 2 by ring] at hm
    push_cast
    linear_combination h1 + 3 * h0 + hm

theorem U_rel' (L : ℕ) (d e f : ℤ) (he : e = d + 1) (hf : f = d - 1) :
    ((L : ℤ) + d + 1) * U L e + 3 * d * U L d - ((L : ℤ) - d + 1) * U L f = 0 := by
  subst he hf; exact U_rel L d

theorem U_out (L : ℕ) : ∀ d : ℤ, (L : ℤ) < d ∨ d < -(L : ℤ) → U L d = 0 := by
  induction L with
  | zero => intro d hd; rw [U_zero, if_neg (by omega)]
  | succ L ih =>
    intro d hd
    push_cast at hd
    rw [U_succ, ih (d - 1) (by omega), ih d (by omega), ih (d + 1) (by omega)]
    ring

theorem U_top (L : ℕ) : U L L = 1 := by
  induction L with
  | zero => rfl
  | succ L ih =>
    push_cast
    rw [U_succ' L ((L : ℤ) + 1) (L : ℤ) ((L : ℤ) + 2) (by ring) (by ring), ih,
      U_out L ((L : ℤ) + 1) (Or.inl (by omega)), U_out L ((L : ℤ) + 2) (Or.inl (by omega))]
    ring

theorem U_bot (L : ℕ) : U L (-(L : ℤ)) = 1 := by rw [U_symm]; exact U_top L

theorem UU (l : ℕ) : U (l + 1) 0 = 3 * U l 0 + 2 * U l 1 := by
  rw [U_succ' l 0 (-1) 1 (by norm_num) (by norm_num), U_symm' l 1 (-1) (by norm_num)]; ring

theorem UV (l : ℕ) : U (l + 1) 1 = U l 0 + 3 * U l 1 + U l 2 :=
  U_succ' l 1 0 2 (by norm_num) (by norm_num)

theorem U_relZ (l : ℕ) (L : ℤ) (hL : L = l) (c d e : ℤ) (hd : d = c + 1) (he : e = c - 1) :
    (L + c + 1) * U l d + 3 * c * U l c - (L - c + 1) * U l e = 0 := by
  subst hL; exact U_rel' l c d e hd he

theorem T_eq2 (n k : ℕ) : T (n + 2) k =
    if k = 0 ∨ k = n + 2 then 1
    else if n + 2 < k then 0
    else if (n + 2) % 2 = 0 then T (n + 1) (k - 1) + T (n + 1) k
    else T (n + 1) (k - 1) + T (n + 1) k + T n (k - 1) := by
  rw [T]

/-- Closed forms for the rows of `T`: `T(2m+1, k) = U(m, k-m) + U(m, k-m-1)` and
`T(2m+2, k) = U(m+1, k-m-1) - U(m, k-m-1)`. -/
theorem TC (m : ℕ) :
    (∀ k : ℕ, k ≤ 2 * m + 1 → T (2 * m + 1) k = U m ((k : ℤ) - m) + U m ((k : ℤ) - m - 1)) ∧
    (∀ k : ℕ, k ≤ 2 * m + 2 →
      T (2 * m + 2) k = U (m + 1) ((k : ℤ) - m - 1) - U m ((k : ℤ) - m - 1)) := by
  induction m with
  | zero =>
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · interval_cases k <;> decide
    · interval_cases k <;> decide
  | succ m ih =>
    obtain ⟨ho, he⟩ := ih
    have hodd : ∀ k : ℕ, k ≤ 2 * (m + 1) + 1 → T (2 * (m + 1) + 1) k =
        U (m + 1) ((k : ℤ) - ((m + 1 : ℕ) : ℤ)) + U (m + 1) ((k : ℤ) - ((m + 1 : ℕ) : ℤ) - 1) := by
      intro k hk
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, T_eq2]
      by_cases hb : k = 0 ∨ k = 2 * m + 1 + 2
      · rw [if_pos hb]
        rcases hb with rfl | rfl
        · have b := U_bot (m + 1)
          have z := U_out (m + 1) (-((m : ℤ) + 1) - 1) (Or.inr (by push_cast; omega))
          push_cast at b ⊢
          ring_nf at b z ⊢
          linear_combination -b - z
        · have t := U_top (m + 1)
          have z := U_out (m + 1) ((m : ℤ) + 2) (Or.inl (by push_cast; omega))
          push_cast at t ⊢
          ring_nf at t z ⊢
          linear_combination -t - z
      · rw [if_neg hb, if_neg (by omega), if_neg (by omega)]
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [Nat.add_sub_cancel, show 2 * m + 1 + 1 = 2 * m + 2 by ring, he j (by omega),
          he (j + 1) (by omega), ho j (by omega)]
        push_cast
        ring_nf
    refine ⟨hodd, fun k hk => ?_⟩
    rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by ring, T_eq2]
    by_cases hb : k = 0 ∨ k = 2 * m + 2 + 2
    · rw [if_pos hb]
      rcases hb with rfl | rfl
      · have b := U_bot (m + 1 + 1)
        have z := U_out (m + 1) (-((m : ℤ) + 2)) (Or.inr (by push_cast; omega))
        push_cast at b ⊢
        ring_nf at b z ⊢
        linear_combination -b + z
      · have t := U_top (m + 1 + 1)
        have z := U_out (m + 1) ((m : ℤ) + 2) (Or.inl (by push_cast; omega))
        push_cast at t ⊢
        ring_nf at t z ⊢
        linear_combination -t + z
    · rw [if_neg hb, if_neg (by omega), if_pos (by omega)]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel, show 2 * m + 2 + 1 = 2 * (m + 1) + 1 by ring, hodd j (by omega),
        hodd (j + 1) (by omega)]
      have s := U_succ' (m + 1) ((j : ℤ) - m - 1) ((j : ℤ) - m - 2) ((j : ℤ) - m) (by ring) (by ring)
      push_cast at s ⊢
      ring_nf at s ⊢
      linear_combination -s

/-- `a (l+1) = U(l,1) + 2 U(l,2) + U(l,3)` for `l ≥ 1`. -/
theorem a_closed (l : ℕ) (hl : 1 ≤ l) : a (l + 1) = U l 1 + 2 * U l 2 + U l 3 := by
  obtain ⟨p, rfl⟩ : ∃ p, l = p + 1 := ⟨l - 1, by omega⟩
  unfold a
  rw [show 2 * (p + 1 + 1) = 2 * (p + 1) + 2 by ring, show p + 1 + 1 - 2 = p by omega,
    (TC (p + 1)).2 p (by omega), show ((p : ℕ) : ℤ) - ((p + 1 : ℕ) : ℤ) - 1 = -2 by push_cast; ring]
  have i1 := U_succ' (p + 1) (-2) (-3) (-1) (by norm_num) (by norm_num)
  have s1 := U_symm' (p + 1) 1 (-1) (by norm_num)
  have s2 := U_symm' (p + 1) 2 (-2) (by norm_num)
  have s3 := U_symm' (p + 1) 3 (-3) (by norm_num)
  linear_combination i1 + s3 + 2 * s2 + s1

end OMA.A026389Proof

open OMA.S_oeis_a026389 OMA.A026389Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a026389.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have h0 : a (m + 5) = U (m + 4) 1 + 2 * U (m + 4) 2 + U (m + 4) 3 := by
    rw [show m + 5 = m + 4 + 1 by omega]; exact a_closed (m + 4) (by omega)
  have h1 : a (m + 5 - 1) = U (m + 3) 1 + 2 * U (m + 3) 2 + U (m + 3) 3 := by
    rw [show m + 5 - 1 = m + 3 + 1 by omega]; exact a_closed (m + 3) (by omega)
  have h2 : a (m + 5 - 2) = U (m + 2) 1 + 2 * U (m + 2) 2 + U (m + 2) 3 := by
    rw [show m + 5 - 2 = m + 2 + 1 by omega]; exact a_closed (m + 2) (by omega)
  have h3 : a (m + 5 - 3) = U (m + 1) 1 + 2 * U (m + 1) 2 + U (m + 1) 3 := by
    rw [show m + 5 - 3 = m + 1 + 1 by omega]; exact a_closed (m + 1) (by omega)
  have h4 : a (m + 5 - 4) = U m 1 + 2 * U m 2 + U m 3 := by
    rw [show m + 5 - 4 = m + 1 by omega]; exact a_closed (m) (by omega)
  rw [h0, h1, h2, h3, h4]
  have r0_2 := U_relZ (m) (m : ℤ) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r0_3 := U_relZ (m) (m : ℤ) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have u1 : U (m + 1) 0 = 3 * U m 0 + 2 * U m 1 := UU (m)
  have v1 : U (m + 1) 1 = U m 0 + 3 * U m 1 + U m 2 := UV (m)
  have r1_2 := U_relZ (m + 1) ((m : ℤ) + 1) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r1_3 := U_relZ (m + 1) ((m : ℤ) + 1) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have u2 : U (m + 2) 0 = 3 * U (m + 1) 0 + 2 * U (m + 1) 1 := UU (m + 1)
  have v2 : U (m + 2) 1 = U (m + 1) 0 + 3 * U (m + 1) 1 + U (m + 1) 2 := UV (m + 1)
  have r2_2 := U_relZ (m + 2) ((m : ℤ) + 2) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r2_3 := U_relZ (m + 2) ((m : ℤ) + 2) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have u3 : U (m + 3) 0 = 3 * U (m + 2) 0 + 2 * U (m + 2) 1 := UU (m + 2)
  have v3 : U (m + 3) 1 = U (m + 2) 0 + 3 * U (m + 2) 1 + U (m + 2) 2 := UV (m + 2)
  have r3_2 := U_relZ (m + 3) ((m : ℤ) + 3) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r3_3 := U_relZ (m + 3) ((m : ℤ) + 3) (by omega) 2 3 1 (by norm_num) (by norm_num)
  have u4 : U (m + 4) 0 = 3 * U (m + 3) 0 + 2 * U (m + 3) 1 := UU (m + 3)
  have v4 : U (m + 4) 1 = U (m + 3) 0 + 3 * U (m + 3) 1 + U (m + 3) 2 := UV (m + 3)
  have r4_2 := U_relZ (m + 4) ((m : ℤ) + 4) (by omega) 1 2 0 (by norm_num) (by norm_num)
  have r4_3 := U_relZ (m + 4) ((m : ℤ) + 4) (by omega) 2 3 1 (by norm_num) (by norm_num)
  push_cast
  have hD : (1 * ((m : ℤ) + 3) * ((m : ℤ) + 4) * ((m : ℤ) + 5) * ((m : ℤ) + 6) : ℤ) ≠ 0 := by positivity
  refine (mul_eq_zero.mp ?_).resolve_left hD
  linear_combination (-5040 + 3612 * (m : ℤ) + 3514 * (m : ℤ) ^ 2 + 798 * (m : ℤ) ^ 3 + 56 * (m : ℤ) ^ 4) * r0_2
      + (4200 + 6790 * (m : ℤ) + 3115 * (m : ℤ) ^ 2 + 560 * (m : ℤ) ^ 3 + 35 * (m : ℤ) ^ 4) * r0_3
      + (3360 + 3752 * (m : ℤ) - 224 * (m : ℤ) ^ 2 - 798 * (m : ℤ) ^ 3 - 196 * (m : ℤ) ^ 4 - 14 * (m : ℤ) ^ 5) * u1
      + (-10080 - 6216 * (m : ℤ) - 2940 * (m : ℤ) ^ 2 - 1120 * (m : ℤ) ^ 3 - 210 * (m : ℤ) ^ 4 - 14 * (m : ℤ) ^ 5) * v1
      + (-7080 - 16276 * (m : ℤ) - 8792 * (m : ℤ) ^ 2 - 1754 * (m : ℤ) ^ 3 - 118 * (m : ℤ) ^ 4) * r1_2
      + (-16920 - 18324 * (m : ℤ) - 7168 * (m : ℤ) ^ 2 - 1196 * (m : ℤ) ^ 3 - 72 * (m : ℤ) ^ 4) * r1_3
      + (-720 + 4176 * (m : ℤ) + 5504 * (m : ℤ) ^ 2 + 2358 * (m : ℤ) ^ 3 + 416 * (m : ℤ) ^ 4 + 26 * (m : ℤ) ^ 5) * u2
      + (12600 + 14580 * (m : ℤ) + 8332 * (m : ℤ) ^ 2 + 2674 * (m : ℤ) ^ 3 + 428 * (m : ℤ) ^ 4 + 26 * (m : ℤ) ^ 5) * v2
      + (12312 + 15588 * (m : ℤ) + 6876 * (m : ℤ) ^ 2 + 1262 * (m : ℤ) ^ 3 + 82 * (m : ℤ) ^ 4) * r2_2
      + (14544 + 14364 * (m : ℤ) + 5218 * (m : ℤ) ^ 2 + 826 * (m : ℤ) ^ 3 + 48 * (m : ℤ) ^ 4) * r2_3
      + (-5472 - 9144 * (m : ℤ) - 5776 * (m : ℤ) ^ 2 - 1742 * (m : ℤ) ^ 3 - 252 * (m : ℤ) ^ 4 - 14 * (m : ℤ) ^ 5) * u3
      + (-8928 - 11880 * (m : ℤ) - 6508 * (m : ℤ) ^ 2 - 1816 * (m : ℤ) ^ 3 - 254 * (m : ℤ) ^ 4 - 14 * (m : ℤ) ^ 5) * v3
      + (-4464 - 4908 * (m : ℤ) - 1980 * (m : ℤ) ^ 2 - 346 * (m : ℤ) ^ 3 - 22 * (m : ℤ) ^ 4) * r3_2
      + (-4080 - 3916 * (m : ℤ) - 1380 * (m : ℤ) ^ 2 - 212 * (m : ℤ) ^ 3 - 12 * (m : ℤ) ^ 4) * r3_3
      + (1920 + 2464 * (m : ℤ) + 1256 * (m : ℤ) ^ 2 + 318 * (m : ℤ) ^ 3 + 40 * (m : ℤ) ^ 4 + 2 * (m : ℤ) ^ 5) * u4
      + (2160 + 2652 * (m : ℤ) + 1304 * (m : ℤ) ^ 2 + 322 * (m : ℤ) ^ 3 + 40 * (m : ℤ) ^ 4 + 2 * (m : ℤ) ^ 5) * v4
      + (480 + 496 * (m : ℤ) + 190 * (m : ℤ) ^ 2 + 32 * (m : ℤ) ^ 3 + 2 * (m : ℤ) ^ 4) * r4_2
      + (360 + 342 * (m : ℤ) + 119 * (m : ℤ) ^ 2 + 18 * (m : ℤ) ^ 3 + (m : ℤ) ^ 4) * r4_3
