import OMAStatements.S_oeis_a179894
import Mathlib

/-!
# A179894: 3 divides a(n) if and only if 3 divides n

Write S(m) for the coefficient of x^m in F * G, so a(n) = S(n - 1). Since u(i + 2) = u(i),
peeling the first two terms off the antidiagonal sum gives
S(m + 2) = S(m) + 2 v(m + 1) + v(m + 2).
With S(0) = 1 and S(1) = 2 this yields S(2k + 2) = 4k + 3 and S(2k + 1) = 5k + 2, the closed
form of the entry (a(n) = 2n - 3 for odd n > 1 and a(n) = 5n/2 - 3 for even n). Both closed
forms are 0 mod 3 exactly when n is, and a(1) = 1.
-/

namespace OMA.P179894

open OMA.S_oeis_a179894 PowerSeries

lemma u_add_two (i : ℕ) : u (i + 2) = u i := by
  unfold u
  have : (i + 2) % 2 = i % 2 := by omega
  rw [this]

/-- The coefficients of F * G as an antidiagonal sum. -/
lemma S_def (m : ℕ) :
    coeff m (F * G) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, u p.1 * v p.2 := by
  rw [coeff_mul]
  simp [F, G]

/-- S(m + 2) = S(m) + 2 v(m + 1) + v(m + 2). -/
lemma S_rec (m : ℕ) :
    coeff (m + 1 + 1) (F * G) = coeff m (F * G) + 2 * v (m + 1) + v (m + 1 + 1) := by
  rw [S_def, S_def, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
  simp only [u_add_two]
  have h0 : u 0 = 1 := rfl
  have h1 : u (0 + 1) = 2 := rfl
  rw [h0, h1]
  ring

lemma S_zero : coeff 0 (F * G) = 1 := by
  rw [S_def]
  rfl

lemma S_one : coeff 1 (F * G) = 2 := by
  rw [S_def]
  rfl

/-- S(2k + 2) = 4k + 3, that is a(n) = 2n - 3 for odd n = 2k + 3. -/
lemma S_even (k : ℕ) : coeff (2 * k + 2) (F * G) = 4 * k + 3 := by
  induction k with
  | zero =>
    have := S_rec 0
    rw [S_zero] at this
    simpa [v] using this
  | succ k ih =>
    have h := S_rec (2 * k + 2)
    have e1 : 2 * (k + 1) + 2 = 2 * k + 2 + 1 + 1 := by ring
    rw [e1, h, ih]
    have hv1 : v (2 * k + 2 + 1) = 1 := by
      unfold v
      have : (2 * k + 2 + 1) % 2 = 1 := by omega
      simp [this]
    have hv2 : v (2 * k + 2 + 1 + 1) = 2 := by
      unfold v
      have : (2 * k + 2 + 1 + 1) % 2 = 0 := by omega
      simp [this]
    rw [hv1, hv2]
    ring

/-- S(2k + 1) = 5k + 2, that is a(n) = 5n/2 - 3 for even n = 2k + 2. -/
lemma S_odd (k : ℕ) : coeff (2 * k + 1) (F * G) = 5 * k + 2 := by
  induction k with
  | zero => simpa using S_one
  | succ k ih =>
    have h := S_rec (2 * k + 1)
    have e1 : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
    rw [e1, h, ih]
    have hv1 : v (2 * k + 1 + 1) = 2 := by
      unfold v
      have : (2 * k + 1 + 1) % 2 = 0 := by omega
      simp [this]
    have hv2 : v (2 * k + 1 + 1 + 1) = 1 := by
      unfold v
      have : (2 * k + 1 + 1 + 1) % 2 = 1 := by omega
      simp [this]
    rw [hv1, hv2]
    ring

theorem sol : type_of% @OMA.S_oeis_a179894.main := by
  intro n hn
  show 3 ∣ coeff (n - 1) (F * G) ↔ n % 3 = 0
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (n - 1)
  · rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      have hn1 : n = 1 := by omega
      subst hn1
      rw [show (1 - 1 : ℕ) = 0 from rfl, S_zero]
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have e : n - 1 = 2 * j + 2 := by omega
      rw [e, S_even]
      omega
  · rw [hk, S_odd]
    omega

end OMA.P179894

theorem OMA.solution : type_of% @OMA.S_oeis_a179894.main := OMA.P179894.sol
