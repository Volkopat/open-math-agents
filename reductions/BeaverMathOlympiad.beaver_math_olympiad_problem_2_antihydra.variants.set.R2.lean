import FormalConjectures.Other.BeaverMathOlympiad
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Factorization.Basic

-- Credit: @Pixelstorm44
/-!
# Antihydra via parity runs

At a prefix ending just before an even term, each completed odd run has
one entry and one exit. The last even term before entry is 2 mod 4, and
the last odd term before exit is 3 mod 4. This lets us bound the two sides
using separate estimates on even and odd terms. -/

namespace OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_variants_set_R2

/-- Average at least 3/2 even terms per completed odd run. -/
def H1 : Prop :=
  ∀ (a : ℕ → ℕ), a 0 = 8 → (∀ n, a (n + 1) = 3 * a n / 2) →
    ∀ n, Even (a n) →
      3 * Nat.count (fun i ↦ a i % 4 = 2) n ≤ 2 * Nat.count (fun i ↦ Even (a i)) n

/-- Average at most three odd terms per completed odd run. -/
def H2 : Prop :=
  ∀ (a : ℕ → ℕ), a 0 = 8 → (∀ n, a (n + 1) = 3 * a n / 2) →
    ∀ n, Even (a n) →
      Nat.count (fun i ↦ Odd (a i)) n ≤ 3 * Nat.count (fun i ↦ a i % 4 = 3) n

private theorem switch_count (a : ℕ → ℕ) (h0 : a 0 = 8)
    (step : ∀ n, a (n + 1) = 3 * a n / 2) (n : ℕ) :
    Nat.count (fun i ↦ a i % 4 = 2) n =
      Nat.count (fun i ↦ a i % 4 = 3) n + a n % 2 := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    simp only [Nat.count_succ, step n]
    have update (x : ℕ) : x % 2 + (if x % 4 = 2 then 1 else 0) =
        (if x % 4 = 3 then 1 else 0) + (3 * x / 2) % 2 := by
      obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r < 4 ∧ x = 4 * q + r :=
        ⟨x / 4, x % 4, Nat.mod_lt _ (by decide), by omega⟩
      interval_cases r <;> simp [mul_add] <;> omega
    have h := update (a n)
    omega

/-- While the current term is odd, subtracting one turns the recurrence
into multiplication by 3/2. Each such step consumes a power of two. -/
private theorem even_after (a : ℕ → ℕ) (step : ∀ n, a (n + 1) = 3 * a n / 2)
    (k n u : ℕ) (hu : Odd u) (hx : a n = 2 ^ k * u + 1) : Even (a (n + k)) := by
  induction k generalizing n u with
  | zero =>
    rw [Nat.add_zero, hx]
    simp only [pow_zero, one_mul]
    obtain ⟨v, hv⟩ := hu
    exact ⟨v + 1, by omega⟩
  | succ k ih =>
    have next : a (n + 1) = 2 ^ k * (3 * u) + 1 := by
      rw [step, hx, pow_succ]
      have h : 3 * (2 ^ k * 2 * u + 1) = 2 * (2 ^ k * (3 * u) + 1) + 1 := by ring
      rw [h]
      omega
    have h := ih (n + 1) (3 * u) ((by decide : Odd 3).mul hu) next
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem main : H1 → H2 → type_of% @BeaverMathOlympiad.beaver_math_olympiad_problem_2_antihydra.variants.set := by
  intro h1 h2 a h0 step n
  have at_even (j : ℕ) (hj : Even (a j)) :
      Nat.count (fun i ↦ Odd (a i)) j ≤ 2 * Nat.count (fun i ↦ Even (a i)) j := by
    have hs := switch_count a h0 step j
    rw [Nat.even_iff.mp hj, Nat.add_zero] at hs
    exact (h2 a h0 step j hj).trans (hs ▸ h1 a h0 step j hj)
  have lower (j : ℕ) : 2 ≤ a j := by
    induction j with
    | zero => omega
    | succ j ih => rw [step]; omega
  obtain ⟨k, u, hu, hk⟩ := Nat.exists_eq_two_pow_mul_odd (n := a n - 1) (by have := lower n; omega)
  have hend := even_after a step k n u hu (by have := lower n; omega)
  rw [Nat.Ico_zero_eq_range, ← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  clear hk hu u
  induction k generalizing n with
  | zero => exact at_even n (by simpa using hend)
  | succ k ih =>
    by_cases hn : Even (a n)
    · exact at_even n hn
    · have h := ih (n + 1) (by simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend)
      simp only [Nat.count_succ, if_neg hn, Nat.add_zero] at h
      omega

end OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_variants_set_R2
