import Mathlib

/-!
# A159227: 1/4 the number of n X n arrays of squares of integers with every 2X2 subblock summing to 27

Source: https://oeis.org/A159227
Credit: @Dariusthedoggie

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-28.
Offset 2 (data 7, 22, 45, 103, 193, 421, 777, 1681, 3097, 6697, ...).

Conventions:
* Any n X n array (`n >= 2`) of squares of integers with every 2 X 2 subblock summing to
  27 has every entry in `{0, 1, ..., 27}`, so it is represented by `x : Fin n → Fin n → Fin 28`
  with every entry a perfect square `∃ k ≤ v, k ^ 2 = v`.
* `total n` is the number of such n X n arrays; for `n >= 2`, `4 ∣ total n` and `a n = total n / 4`.
* `a 0 = 0` and `a 1 = 0` are conventions outside the offset; they do not affect the
  generating function.
* The generating function is stated after multiplication by its denominator, whose constant
  term is `-1` (a unit in `ℚ`).

Conjecture in the formula section (Maksym Voznyy, Jul 26 2009):
Conjecture: G.f.: x^2*(-7-8*x^4+32*x^3+19*x^2-15*x)/((x-1)*(2*x+1)*(2*x-1)*(2*x^2-1)).
-/

namespace OMA.S_oeis_a159227

open PowerSeries

/-- A natural number `v` is the square of an integer. -/
def isSquare (v : ℕ) : Prop :=
  ∃ k ≤ v, k ^ 2 = v

instance (v : ℕ) : Decidable (isSquare v) := by
  unfold isSquare; infer_instance

/-- An n X n array of squares of integers (bounded by 27) with every 2 X 2 subblock summing
to 27. -/
def isValid {n : ℕ} (x : Fin n → Fin n → Fin 28) : Prop :=
  (∀ i j : Fin n, isSquare (x i j : ℕ)) ∧
  (∀ (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n),
    (x ⟨i, by omega⟩ ⟨j, by omega⟩ : ℕ) +
    (x ⟨i, by omega⟩ ⟨j + 1, hj⟩ : ℕ) +
    (x ⟨i + 1, hi⟩ ⟨j, by omega⟩ : ℕ) +
    (x ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ : ℕ) = 27)

instance {n : ℕ} (x : Fin n → Fin n → Fin 28) : Decidable (isValid x) := by
  unfold isValid
  haveI : Decidable (∀ (i j : ℕ) (hi : i + 1 < n) (hj : j + 1 < n),
    (x ⟨i, by omega⟩ ⟨j, by omega⟩ : ℕ) +
    (x ⟨i, by omega⟩ ⟨j + 1, hj⟩ : ℕ) +
    (x ⟨i + 1, hi⟩ ⟨j, by omega⟩ : ℕ) +
    (x ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ : ℕ) = 27) :=
    decidable_of_iff
      (∀ i j : Fin n, ∀ (hi : (i : ℕ) + 1 < n) (hj : (j : ℕ) + 1 < n),
        (x i j : ℕ) + (x i ⟨(j : ℕ) + 1, hj⟩ : ℕ) +
        (x ⟨(i : ℕ) + 1, hi⟩ j : ℕ) + (x ⟨(i : ℕ) + 1, hi⟩ ⟨(j : ℕ) + 1, hj⟩ : ℕ) = 27)
      ⟨fun h i j hi hj => h ⟨i, by omega⟩ ⟨j, by omega⟩ hi hj,
       fun h i j hi hj => h i.1 j.1 hi hj⟩
  infer_instance

/-- Total number of valid n X n arrays. -/
def total (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin n → Fin 28 => isValid x)).card

/-- A159227: 1/4 the number of n X n arrays of squares of integers with every 2 X 2 subblock
summing to 27. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n => total n / 4

theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((X - 1) * (2 * X + 1) * (2 * X - 1) * (2 * X ^ 2 - 1)) =
    X ^ 2 * (-7 - 8 * X ^ 4 + 32 * X ^ 3 + 19 * X ^ 2 - 15 * X) := by
  sorry

end OMA.S_oeis_a159227
