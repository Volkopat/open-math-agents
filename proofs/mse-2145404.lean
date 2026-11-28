import OMAStatements.S_mse_2145404
import Mathlib

open OMA.S_mse_2145404

namespace OMA.P_mse_2145404

def U (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => a * U a b (n + 1) + b * U a b n

theorem U_zero (a b : ℕ) : U a b 0 = 0 := rfl
theorem U_one (a b : ℕ) : U a b 1 = 1 := rfl
theorem U_add_two (a b n : ℕ) : U a b (n + 2) = a * U a b (n + 1) + b * U a b n := rfl

theorem U_add (a b : ℕ) (m n : ℕ) :
    U a b (m + n + 1) = U a b (m + 1) * U a b (n + 1) + b * U a b m * U a b n := by
  induction n generalizing m with
  | zero => simp [U_one, U_zero]
  | succ n ih =>
    specialize ih (m + 1)
    have e : m + 1 + n + 1 = m + (n + 1) + 1 := by omega
    rw [e] at ih
    rw [ih, U_add_two, U_add_two]
    ring

theorem U_cop_b (a b : ℕ) (hab : Nat.Coprime a b) : ∀ n, Nat.Coprime (U a b (n + 1)) b := by
  intro n
  induction n with
  | zero => simp [U_one]
  | succ n ih =>
    rw [U_add_two]
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_add_mul_left_right, Nat.gcd_comm]
    exact Nat.Coprime.mul_left hab ih

theorem U_cop_succ (a b : ℕ) (hab : Nat.Coprime a b) : ∀ n, Nat.Coprime (U a b n) (U a b (n + 1)) := by
  intro n
  induction n with
  | zero => simp [U_one, U_zero]
  | succ n ih =>
    rw [Nat.Coprime, U_add_two, Nat.gcd_comm, add_comm, Nat.gcd_add_mul_right_left]
    have h1 : Nat.Coprime (b * U a b n) (U a b (n + 1)) :=
      Nat.Coprime.mul_left (U_cop_b a b hab n).symm ih
    exact h1

theorem gcd_U_add_self (a b : ℕ) (hab : Nat.Coprime a b) (m n : ℕ) :
    Nat.gcd (U a b m) (U a b (n + m)) = Nat.gcd (U a b m) (U a b n) := by
  rcases n with _ | n
  · simp [U_zero]
  have e : n + 1 + m = n + m + 1 := by omega
  rw [e, U_add]
  have e2 : U a b (n + 1) * U a b (m + 1) + b * U a b n * U a b m
      = U a b (n + 1) * U a b (m + 1) + (b * U a b n) * U a b m := rfl
  rw [e2, Nat.gcd_add_mul_right_right]
  exact Nat.Coprime.gcd_mul_right_cancel_right _ (U_cop_succ a b hab m).symm

theorem gcd_U_add_mul_self (a b : ℕ) (hab : Nat.Coprime a b) (m n : ℕ) :
    ∀ k, Nat.gcd (U a b m) (U a b (n + k * m)) = Nat.gcd (U a b m) (U a b n)
  | 0 => by simp
  | k + 1 => by
    rw [← gcd_U_add_mul_self a b hab m n k, add_mul, ← add_assoc, one_mul, gcd_U_add_self a b hab]

theorem U_gcd (a b : ℕ) (hab : Nat.Coprime a b) (m n : ℕ) :
    U a b (Nat.gcd m n) = Nat.gcd (U a b m) (U a b n) := by
  induction m, n using Nat.gcd.induction with
  | H0 => simp [U_zero]
  | H1 m n _ h' =>
    rw [← Nat.gcd_rec m n] at h'
    conv_rhs => rw [← Nat.mod_add_div' n m]
    rwa [gcd_U_add_mul_self a b hab m (n % m) (n / m), Nat.gcd_comm (U a b m) _]

theorem F_eq (a b : ℕ) (F : ℕ → ℕ) (h0 : F 0 = 0)
    (hrec : ∀ i : ℕ, F (i + 2) = a * F (i + 1) + b * F i) : ∀ n, F n = F 1 * U a b n ∧ F (n + 1) = F 1 * U a b (n + 1) := by
  intro n
  induction n with
  | zero => exact ⟨by simp [h0, U_zero], by simp [U_one]⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [hrec, U_add_two, ih.1, ih.2]
    ring

end OMA.P_mse_2145404

open OMA.P_mse_2145404 in
theorem OMA.solution : type_of% @OMA.S_mse_2145404.main := by
  intro a b _ _ hab F h0 _ hrec m n
  rw [(F_eq a b F h0 hrec (Nat.gcd m n)).1, (F_eq a b F h0 hrec n).1, (F_eq a b F h0 hrec m).1,
    Nat.gcd_mul_left, U_gcd a b hab, Nat.gcd_comm]
