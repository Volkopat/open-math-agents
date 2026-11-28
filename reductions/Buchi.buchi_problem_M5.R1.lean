import FormalConjectures.Wikipedia.Buchi

-- Reduction Buchi.buchi_problem_M5.R1 of Büchi's problem (first open case, $M = 5$)
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Büchi's problem for five squares

The target: if `(x + n)^2 + a` is a square for `n = 0, 1, 2, 3, 4`, then `a = 0`.

`main` proves, for a solution with `a ≠ 0`:
* Symmetry: `x ↦ -x - 4` reverses the five bases, so one may take `x ≥ -2`.
* Sign: `a < 0`. Two consecutive nonnegative bases `z, z + 1` with `a > 0` would give roots
  `z < R < S` with `S^2 - R^2 = 2z + 1`, while `S ≥ R + 1` forces `S^2 - R^2 ≥ 2R + 1 ≥ 2z + 3`.
* Factorization: for consecutive nonnegative bases `z, z + 1`, `2z + 1 = (S - R)(S + R)` with
  `2 ≤ S - R ≤ S + R`, since `S - R = 1` forces `R = z`, that is `a = 0`. So `2z + 1` is
  composite. This rules out `x ∈ {-2, -1, 0}`, and for `x ≥ 1` it makes the four consecutive
  odd numbers `2x + 1, 2x + 3, 2x + 5, 2x + 7` composite.
* Local obstruction: `a ≡ 0` modulo `64`, `9`, `25` and `7` (finite residue checks in `ZMod`),
  so `100800 ∣ a`. These are the exact conditions at `2, 3, 5, 7`: modulo `128`, `27`, `125`
  and `49` further residues survive.

What remains, under all these side conditions:
* `H1`: no solution with `1 ≤ x ≤ 10^6`. This is a finite statement, since `x` bounds `a`.
  A search over `x ≤ 5 · 10^6` finds 40 nontrivial sequences of length four (the first is
  `x = 246`, `a = -60480`, with roots `6, 23, 32, 39`) and none of length five.
* `H2`: no solution with `x > 10^6`. This is the open core.
-/

namespace OMA.R_Buchi_buchi_problem_M5_R1

open Buchi

/-- No nontrivial Büchi sequence of length five with base point `1 ≤ x ≤ 10^6`. The side
conditions (`a < 0`, `100800 ∣ a`, four composite odd numbers) are proved by `main` for every
solution with `a ≠ 0`. -/
def H1 : Prop :=
  ∀ (x : ℕ) (a : ℤ), 1 ≤ x → x ≤ 10 ^ 6 → a < 0 → 100800 ∣ a →
    (∀ n : ℕ, n < 4 → ¬ (2 * x + 2 * n + 1).Prime) →
    ¬ ∀ n ∈ Finset.range 5, IsSquare (((x : ℤ) + n) ^ 2 + a)

/-- No nontrivial Büchi sequence of length five with base point `x > 10^6`, under the same side
conditions. -/
def H2 : Prop :=
  ∀ (x : ℕ) (a : ℤ), 10 ^ 6 < x → a < 0 → 100800 ∣ a →
    (∀ n : ℕ, n < 4 → ¬ (2 * x + 2 * n + 1).Prime) →
    ¬ ∀ n ∈ Finset.range 5, IsSquare (((x : ℤ) + n) ^ 2 + a)

/-- Modulo `7`, five consecutive values `(X + n)^2 + A` are all squares only when `A = 0`. -/
lemma res7 : ∀ X A : ZMod 7, IsSquare (X ^ 2 + A) → IsSquare ((X + 1) ^ 2 + A) →
    IsSquare ((X + 2) ^ 2 + A) → IsSquare ((X + 3) ^ 2 + A) → IsSquare ((X + 4) ^ 2 + A) →
    A = 0 := by
  decide

/-- The same modulo `9`. -/
lemma res9 : ∀ X A : ZMod 9, IsSquare (X ^ 2 + A) → IsSquare ((X + 1) ^ 2 + A) →
    IsSquare ((X + 2) ^ 2 + A) → IsSquare ((X + 3) ^ 2 + A) → IsSquare ((X + 4) ^ 2 + A) →
    A = 0 := by
  decide

/-- The same modulo `25`. -/
lemma res25 : ∀ X A : ZMod 25, IsSquare (X ^ 2 + A) → IsSquare ((X + 1) ^ 2 + A) →
    IsSquare ((X + 2) ^ 2 + A) → IsSquare ((X + 3) ^ 2 + A) → IsSquare ((X + 4) ^ 2 + A) →
    A = 0 := by
  decide +kernel

/-- The same modulo `64`. -/
lemma res64 : ∀ X A : ZMod 64, IsSquare (X ^ 2 + A) → IsSquare ((X + 1) ^ 2 + A) →
    IsSquare ((X + 2) ^ 2 + A) → IsSquare ((X + 3) ^ 2 + A) → IsSquare ((X + 4) ^ 2 + A) →
    A = 0 := by
  decide +kernel

/-- A residue obstruction modulo `M` gives `M ∣ a`. -/
lemma dvd_of_res {x a : ℤ} (h : ∀ n ∈ Finset.range 5, IsSquare ((x + n) ^ 2 + a)) (M : ℕ)
    [NeZero M]
    (hres : ∀ X A : ZMod M, IsSquare (X ^ 2 + A) → IsSquare ((X + 1) ^ 2 + A) →
      IsSquare ((X + 2) ^ 2 + A) → IsSquare ((X + 3) ^ 2 + A) →
      IsSquare ((X + 4) ^ 2 + A) → A = 0) :
    (M : ℤ) ∣ a := by
  have hm : ∀ n ∈ Finset.range 5,
      IsSquare (((x : ZMod M) + (n : ZMod M)) ^ 2 + (a : ZMod M)) := by
    intro n hn
    have h' := (h n hn).map (Int.castRingHom (ZMod M))
    simpa using h'
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine hres (x : ZMod M) (a : ZMod M) ?_ ?_ ?_ ?_ ?_
  · simpa using hm 0 (by simp)
  · simpa using hm 1 (by simp)
  · simpa using hm 2 (by simp)
  · simpa using hm 3 (by simp)
  · simpa using hm 4 (by simp)

/-- The local obstruction at `2, 3, 5, 7`: `100800 = 64 · 9 · 25 · 7` divides `a`. -/
lemma dvd_100800 {x a : ℤ} (h : ∀ n ∈ Finset.range 5, IsSquare ((x + n) ^ 2 + a)) :
    (100800 : ℤ) ∣ a := by
  have h7 := dvd_of_res h 7 res7
  have h9 := dvd_of_res h 9 res9
  have h25 := dvd_of_res h 25 res25
  have h64 := dvd_of_res h 64 res64
  push_cast at h7 h9 h25 h64
  have e1 : IsCoprime (64 : ℤ) 9 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    rfl
  have e2 : IsCoprime (64 * 9 : ℤ) 25 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    rfl
  have e3 : IsCoprime (64 * 9 * 25 : ℤ) 7 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    rfl
  have h' := e3.mul_dvd (e2.mul_dvd (e1.mul_dvd h64 h9) h25) h7
  norm_num at h'
  exact h'

/-- Roots of `z^2 + a` and `(z + 1)^2 + a`, taken nonnegative. -/
lemma roots {z : ℕ} {a : ℤ} (h1 : IsSquare ((z : ℤ) ^ 2 + a))
    (h2 : IsSquare (((z : ℤ) + 1) ^ 2 + a)) :
    ∃ R S : ℤ, 0 ≤ R ∧ 0 ≤ S ∧ (z : ℤ) ^ 2 + a = R * R ∧ ((z : ℤ) + 1) ^ 2 + a = S * S := by
  obtain ⟨r, hr⟩ := h1
  obtain ⟨s, hs⟩ := h2
  exact ⟨|r|, |s|, abs_nonneg r, abs_nonneg s, by rw [hr, abs_mul_abs_self],
    by rw [hs, abs_mul_abs_self]⟩

/-- Two consecutive nonnegative bases already force `a ≤ 0`. -/
lemma not_pos {z : ℕ} {a : ℤ} (h1 : IsSquare ((z : ℤ) ^ 2 + a))
    (h2 : IsSquare (((z : ℤ) + 1) ^ 2 + a)) : ¬ 0 < a := by
  intro ha
  obtain ⟨R, S, hR0, hS0, hR, hS⟩ := roots h1 h2
  have hz0 : (0 : ℤ) ≤ z := Int.natCast_nonneg z
  have h3 : (z : ℤ) < R := by nlinarith
  have h4 : R < S := by nlinarith
  have h3' : (z : ℤ) + 1 ≤ R := h3
  have h4' : R + 1 ≤ S := h4
  have h5 : (R + 1) * (R + 1) ≤ S * S := mul_self_le_mul_self (by linarith) h4'
  nlinarith

/-- For consecutive nonnegative bases `z, z + 1` and `a ≠ 0`, the odd number `2z + 1` is
composite: it is `(S - R)(S + R)` with both factors at least `2`. -/
lemma composite {z : ℕ} {a : ℤ} (h1 : IsSquare ((z : ℤ) ^ 2 + a))
    (h2 : IsSquare (((z : ℤ) + 1) ^ 2 + a)) (ha : a ≠ 0) :
    z ≠ 0 ∧ ¬ (2 * z + 1).Prime := by
  obtain ⟨R, S, hR0, hS0, hR, hS⟩ := roots h1 h2
  have hz0 : (0 : ℤ) ≤ z := Int.natCast_nonneg z
  have hprod : (S - R) * (S + R) = 2 * (z : ℤ) + 1 := by nlinarith
  have hpos : 0 < S - R := by
    by_contra hle
    have hle' : S - R ≤ 0 := not_lt.mp hle
    have : (S - R) * (S + R) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle' (by linarith)
    linarith
  have hne1 : S - R ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hprod
    apply ha
    have hRz : R = z := by linarith
    rw [hRz] at hR
    nlinarith
  have ht2 : 2 ≤ S - R := by omega
  have hu2 : 2 ≤ S + R := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = S - R := ⟨(S - R).toNat, Int.toNat_of_nonneg (by linarith)⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ, (u : ℤ) = S + R := ⟨(S + R).toNat, Int.toNat_of_nonneg (by linarith)⟩
  have hnat : t * u = 2 * z + 1 := by
    have h' : ((t * u : ℕ) : ℤ) = ((2 * z + 1 : ℕ) : ℤ) := by
      push_cast
      rw [ht, hu]
      exact hprod
    exact_mod_cast h'
  have ht2' : 2 ≤ t := by omega
  have hu2' : 2 ≤ u := by omega
  refine ⟨?_, ?_⟩
  · intro hz
    subst hz
    nlinarith
  · rw [← hnat]
    exact Nat.not_prime_mul (by omega) (by omega)

theorem main : H1 → H2 → type_of% @Buchi.buchi_problem_M5 := by
  intro h1 h2
  unfold IsBuchi
  intro x a hsq
  by_contra ha
  -- Symmetry: move the base point to `y ≥ -2`.
  obtain ⟨y, hy, hsy⟩ : ∃ y : ℤ, 0 ≤ y + 2 ∧
      ∀ n ∈ Finset.range 5, IsSquare ((y + n) ^ 2 + a) := by
    by_cases hx : 0 ≤ x + 2
    · exact ⟨x, hx, hsq⟩
    · refine ⟨-x - 4, by omega, fun n hn => ?_⟩
      have hn4 : n ≤ 4 := by
        rw [Finset.mem_range] at hn
        omega
      have h' := hsq (4 - n) (by rw [Finset.mem_range]; omega)
      have e : (-x - 4 + (n : ℤ)) ^ 2 + a = (x + ((4 - n : ℕ) : ℤ)) ^ 2 + a := by
        rw [Nat.cast_sub hn4]
        push_cast
        ring
      rw [e]
      exact h'
  -- Two consecutive bases `y + n`, `y + n + 1`, when `y + n ≥ 0`.
  have pair : ∀ n : ℕ, n < 4 → ∀ z : ℕ, (z : ℤ) = y + n →
      IsSquare ((z : ℤ) ^ 2 + a) ∧ IsSquare (((z : ℤ) + 1) ^ 2 + a) := by
    intro n hn z hz
    refine ⟨?_, ?_⟩
    · rw [hz]
      exact hsy n (by rw [Finset.mem_range]; omega)
    · have h' := hsy (n + 1) (by rw [Finset.mem_range]; omega)
      rw [hz]
      push_cast at h'
      rwa [← add_assoc] at h'
  have hneg : a < 0 := by
    obtain ⟨hA, hB⟩ := pair 2 (by norm_num) (y + 2).toNat (by push_cast; omega)
    have := not_pos hA hB
    omega
  have hy1 : 1 ≤ y := by
    by_contra hlt
    obtain ⟨hA, hB⟩ := pair (-y).toNat (by omega) 0 (by push_cast; omega)
    exact (composite hA hB ha).1 rfl
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, y = m := ⟨y.toNat, by omega⟩
  have hcomp : ∀ n : ℕ, n < 4 → ¬ (2 * m + 2 * n + 1).Prime := by
    intro n hn
    obtain ⟨hA, hB⟩ := pair n hn (m + n) (by push_cast; ring)
    have h' := (composite hA hB ha).2
    rwa [show 2 * (m + n) + 1 = 2 * m + 2 * n + 1 by ring] at h'
  have hdvd := dvd_100800 hsy
  rcases le_or_gt m (10 ^ 6) with hm | hm
  · exact h1 m a (by omega) hm hneg hdvd hcomp hsy
  · exact h2 m a hm hneg hdvd hcomp hsy

end OMA.R_Buchi_buchi_problem_M5_R1
