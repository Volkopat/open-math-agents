import OMAStatements.S_oeis_a377111
import Mathlib

-- The argument follows the accepted disproof of OEIS A377109 (finite orbit of the coordinates
-- modulo a prime), here modulo 2: the coordinates mod 2 alternate between (1,0,0,0) and
-- (0,1,1,0), so 2 divides a(n) exactly for even n, the gaps are all 2, so 1 is a period and the
-- displayed period (3,3,1,2,2,1) of length 6 for p = 2 is not minimal.

namespace OMA.P_a377111
open OMA.S_oeis_a377111

lemma par (n : ℕ) : (coords n).1 % 2 = (n+1) % 2 ∧ (coords n).2.1 % 2 = n % 2 ∧
    (coords n).2.2.1 % 2 = n % 2 ∧ (coords n).2.2.2 % 2 = 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [coords]
    rcases h : coords n with ⟨a, b, c, d⟩
    rw [h] at ih
    simp only at ih ⊢
    omega

lemma dvd_iff (n : ℕ) : 2 ∣ a n ↔ n % 2 = 0 := by
  have := (par n).2.2.1
  unfold a
  omega

lemma k_eq (k : ℕ → ℕ) (hk : StrictMono k) (hits : ∀ n : ℕ, 2 ∣ a n ↔ ∃ j : ℕ, k j = n) :
    ∀ j, k j = 2 * j := by
  intro j
  induction j with
  | zero =>
    obtain ⟨i, hi⟩ := (hits 0).1 ((dvd_iff 0).2 rfl)
    have := hk.monotone (Nat.zero_le i)
    omega
  | succ j ih =>
    obtain ⟨i, hi⟩ := (hits (2*j+2)).1 ((dvd_iff _).2 (by omega))
    have hji : j < i := hk.lt_iff_lt.1 (by omega)
    have h1 : k (j+1) ≤ k i := hk.monotone hji
    have h2 : k j < k (j+1) := hk (by omega)
    have h3 := (dvd_iff (k (j+1))).1 ((hits _).2 ⟨j+1, rfl⟩)
    omega

end OMA.P_a377111

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a377111.main) := by
  intro claim
  obtain ⟨k, hk, hits, _, hw⟩ := claim 2 Nat.prime_two
  obtain ⟨_, _, hmin⟩ := hw [3, 3, 1, 2, 2, 1] (by simp [OMA.S_oeis_a377111.displayed])
  have e := OMA.P_a377111.k_eq k hk hits
  have h1 : OMA.S_oeis_a377111.purePeriod k 1 := by
    refine ⟨Nat.one_pos, fun j => ?_⟩
    simp only [OMA.S_oeis_a377111.gap, e]
    omega
  have := hmin 1 h1
  simp at this
