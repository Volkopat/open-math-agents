import OMAStatements.S_oeis_a362602
import Mathlib

/-!
The final counting step follows the accepted proof of the template entry OEIS A265735: a set
of good rational approximations injects into a bounded set of numerator/denominator pairs.
Here the approximations are those with `|2 pi - q| < 1 / (2 q.den^2)` (Vahlen-type bound),
obtained from a Stern-Brocot (Farey neighbour) descent towards `2 pi`; by Legendre's theorem
(`Real.exists_rat_eq_convergent`) each one is a convergent of `2 pi`, and its numerator lies in
the interval for `k = 2 q.den`.
-/

namespace OMA.P_oeis_a362602

/-- Stern-Brocot descent: Farey neighbours `a/b < ξ < c/d` with `b c - a d = 1` and `b + d`
arbitrarily large. -/
lemma descent {ξ : ℝ} (hξ : Irrational ξ) (N : ℕ) :
    ∃ a b c d : ℤ, 0 < b ∧ 0 < d ∧ b * c - a * d = 1 ∧ (a : ℝ) / b < ξ ∧ ξ < (c : ℝ) / d ∧
      (N : ℤ) ≤ b + d := by
  induction N with
  | zero =>
    refine ⟨⌊ξ⌋, 1, ⌊ξ⌋ + 1, 1, one_pos, one_pos, by ring, ?_, ?_, by norm_num⟩
    · simp only [Int.cast_one, div_one]
      exact lt_of_le_of_ne (Int.floor_le ξ) (fun h => hξ.ne_int ⌊ξ⌋ h.symm)
    · push_cast
      simp [Int.lt_floor_add_one ξ]
  | succ N ih =>
    obtain ⟨a, b, c, d, hb, hd, hdet, h1, h2, hN⟩ := ih
    have hm : ξ ≠ ((a + c : ℤ) : ℝ) / ((b + d : ℤ) : ℝ) := by
      intro h
      apply hξ.ne_rat (((a + c : ℤ) : ℚ) / ((b + d : ℤ) : ℚ))
      rw [h]
      push_cast
      ring
    rcases lt_or_gt_of_ne hm with h | h
    · exact ⟨a, b, a + c, b + d, hb, by omega, by linear_combination hdet, h1, h,
        by push_cast; omega⟩
    · exact ⟨a + c, b + d, c, d, by omega, hd, by linear_combination hdet, h, h2,
        by push_cast; omega⟩

/-- One of two Farey neighbours around an irrational `ξ` is a Vahlen approximation. -/
lemma good {ξ : ℝ} (hξ : Irrational ξ) {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c - a * d = 1) (h1 : (a : ℝ) / b < ξ) (h2 : ξ < (c : ℝ) / d) :
    |ξ - a / b| < 1 / (2 * (b : ℝ) ^ 2) ∨ |ξ - c / d| < 1 / (2 * (d : ℝ) ^ 2) := by
  by_contra hc
  push Not at hc
  obtain ⟨k1, k2⟩ := hc
  rw [abs_of_pos (by linarith)] at k1
  rw [abs_of_neg (by linarith)] at k2
  have hB : (0 : ℝ) < b := by exact_mod_cast hb
  have hD : (0 : ℝ) < d := by exact_mod_cast hd
  set u : ℝ := 1 / b with hu
  set v : ℝ := 1 / d with hv
  have hab : (a : ℝ) / b = a * u := by rw [hu]; ring
  have hcd : (c : ℝ) / d = c * v := by rw [hv]; ring
  have hdetR : (b : ℝ) * c - a * d = 1 := by exact_mod_cast hdet
  have hdiff : (c : ℝ) * v - a * u = u * v := by
    rw [hu, hv]; field_simp; linear_combination hdetR
  have e1 : 1 / (2 * (b : ℝ) ^ 2) = u ^ 2 / 2 := by rw [hu]; field_simp
  have e2 : 1 / (2 * (d : ℝ) ^ 2) = v ^ 2 / 2 := by rw [hv]; field_simp
  rw [e1, hab] at k1
  rw [e2, hcd] at k2
  rw [hab] at h1
  have huv : u = v := by nlinarith [sq_nonneg (u - v)]
  have hx : ξ = a * u + u ^ 2 / 2 := by rw [← huv] at k2 hdiff; nlinarith
  apply hξ.ne_rat ((a : ℚ) / b + 1 / (2 * (b : ℚ) ^ 2))
  rw [hx, hu]
  push_cast
  ring

lemma den_le (a b : ℤ) (hb : 0 < b) : ((Rat.divInt a b).den : ℤ) ≤ b :=
  Int.le_of_dvd hb (Rat.den_dvd a b)

/-- For irrational `ξ` there are infinitely many rationals `q` with
`|ξ - q| < 1 / (2 q.den^2)`. -/
lemma approx {ξ : ℝ} (hξ : Irrational ξ) :
    Set.Infinite {q : ℚ | |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)} := by
  intro hfin
  obtain ⟨M, hM⟩ := (hfin.image (fun q : ℚ => 1 / |ξ - q|)).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (M + 1)
  obtain ⟨a, b, c, d, hb, hd, hdet, h1, h2, hbd⟩ := descent hξ N
  have hB : (0 : ℝ) < b := by exact_mod_cast hb
  have hD : (0 : ℝ) < d := by exact_mod_cast hd
  have hdetR : (b : ℝ) * c - a * d = 1 := by exact_mod_cast hdet
  have hdiff : (c : ℝ) / d - a / b = 1 / (b * d) := by
    field_simp; linear_combination hdetR
  have hprod : ((N : ℤ) : ℝ) - 1 ≤ (b : ℝ) * d := by
    have : (N : ℤ) - 1 ≤ b * d := by nlinarith
    exact_mod_cast this
  -- a member `q = x / y` of the set with distance less than `1 / (b d)` gives a contradiction
  have finish : ∀ x y : ℤ, 0 < y → |ξ - (x : ℝ) / y| < 1 / (2 * (y : ℝ) ^ 2) →
      |ξ - (x : ℝ) / y| < 1 / (b * d) → False := by
    intro x y hy hg hdist
    have hY : (0 : ℝ) < y := by exact_mod_cast hy
    have hq : ((Rat.divInt x y : ℚ) : ℝ) = (x : ℝ) / y := by
      rw [Rat.divInt_eq_div]; push_cast; rfl
    have hden : ((Rat.divInt x y).den : ℝ) ≤ y := by exact_mod_cast den_le x y hy
    have hden0 : (0 : ℝ) < (Rat.divInt x y).den := by exact_mod_cast (Rat.divInt x y).den_pos
    have hmem : Rat.divInt x y ∈ {q : ℚ | |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)} := by
      show |ξ - ((Rat.divInt x y : ℚ) : ℝ)| < 1 / (2 * ((Rat.divInt x y).den : ℝ) ^ 2)
      rw [hq]
      calc |ξ - (x : ℝ) / y| < 1 / (2 * (y : ℝ) ^ 2) := hg
        _ ≤ 1 / (2 * ((Rat.divInt x y).den : ℝ) ^ 2) := by gcongr
    have hle := hM ⟨_, hmem, rfl⟩
    simp only [hq] at hle
    have hpos : 0 < |ξ - (x : ℝ) / y| := by
      rw [abs_pos, sub_ne_zero]
      intro h
      apply hξ.ne_rat ((x : ℚ) / y)
      rw [h]; push_cast; rfl
    have : (b : ℝ) * d < 1 / |ξ - (x : ℝ) / y| := by
      rw [lt_div_iff₀ hpos]
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < b * d)).mp
        (by simpa [one_div] using hdist : |ξ - (x : ℝ) / y| < 1 / (b * d))
      linarith
    push_cast at hprod
    linarith
  rcases good hξ hb hd hdet h1 h2 with g | g
  · refine finish a b hb g ?_
    rw [abs_of_pos (by linarith)]
    linarith
  · refine finish c d hd g ?_
    rw [abs_of_neg (by linarith)]
    linarith

end OMA.P_oeis_a362602

open OMA.S_oeis_a362602 in
theorem OMA.solution : type_of% @OMA.S_oeis_a362602.main := by
  intro hT
  have hirr : Irrational (2 * Real.pi) := by
    simpa using irrational_pi.natCast_mul (two_ne_zero)
  have hS := OMA.P_oeis_a362602.approx hirr
  obtain ⟨B, hB⟩ := hT.bddAbove
  have key : ∀ q : ℚ, |2 * Real.pi - q| < 1 / (2 * (q.den : ℝ) ^ 2) →
      q.num ∈ numerators ∧ (q.den : ℤ) < q.num := by
    intro q hq
    have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hd1 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
    have hqq : (q : ℝ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
    have e : |Real.pi * ((2 * q.den : ℕ) : ℝ) - q.num| = |2 * Real.pi - q| * q.den := by
      rw [hqq, ← abs_of_pos hd, ← abs_mul, abs_of_pos hd]; congr 1; push_cast; field_simp
    have h2 : |Real.pi * ((2 * q.den : ℕ) : ℝ) - q.num| < 1 / ((2 * q.den : ℕ) : ℝ) := by
      rw [e]
      calc |2 * Real.pi - q| * q.den < 1 / (2 * (q.den : ℝ) ^ 2) * q.den := by gcongr
        _ = 1 / ((2 * q.den : ℕ) : ℝ) := by push_cast; field_simp
    obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent hq
    refine ⟨⟨⟨n, by rw [← hn]⟩, ⟨2 * q.den, by have := q.den_pos; omega, h2.le⟩⟩, ?_⟩
    have h3 := (abs_lt.mp hq).2
    have h4 : 1 / (2 * (q.den : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    have := Real.pi_gt_three
    have hq5 : (5 : ℝ) < q := by linarith
    have : (q.den : ℝ) < q.num := by
      rw [hqq] at hq5
      rw [lt_div_iff₀ hd] at hq5
      linarith
    exact_mod_cast this
  apply hS
  apply Set.Finite.of_finite_image (f := fun q : ℚ => (q.num, q.den))
  · apply Set.Finite.subset ((Set.finite_Icc (-1 : ℤ) B).prod (Set.finite_Iic B.toNat))
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨h1, h2⟩ := key q hq
    have h5 := hB h1
    have : (0:ℤ) < q.den := by exact_mod_cast q.den_pos
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Iic]
    refine ⟨⟨by omega, h5⟩, by omega⟩
  · intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    exact Rat.ext h.1 h.2
