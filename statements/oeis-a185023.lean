import Mathlib

/-!
# A185023: Number of steps to reach the number 1 of the map n -> n/3 if x==0 (mod 3), n -> (4n-1)/3 if x==1 (mod 3), n -> (4n+1)/3 if x==2 (mod 3).

Source: https://oeis.org/A185023
Credit: @luciusacarr

Data: 0, 2, 1, 5, 4, 3, 3, 7, 2, 21, 6, 6, 20, 10, 5, 5, 19, 4, 9, 4, ... (offset 1).

Conjecture (Farhad Banazadeh, Sep 15 2026): every positive integer reaches 1 (verified up to
10^11). `main` states it.

Reading of the source:
* The map is `f(n) = n/3` if `n ≡ 0 (mod 3)`, `(4n - 1)/3` if `n ≡ 1 (mod 3)` and `(4n + 1)/3`
  if `n ≡ 2 (mod 3)`; each case is an exact division, so ℕ division is exact here.
* "Reaches 1" means some iterate `f^[k] n` (k ≥ 0) equals 1; for n = 1 this holds with k = 0,
  matching a(1) = 0. The example 8 -> 11 -> 15 -> 5 -> 7 -> 9 -> 3 -> 1 and the first 29 data
  values were checked numerically against this map.
-/

namespace OMA.S_oeis_a185023

/-- The map of A185023. -/
def f (n : ℕ) : ℕ :=
  if n % 3 = 0 then n / 3 else if n % 3 = 1 then (4 * n - 1) / 3 else (4 * n + 1) / 3

theorem main :
    -- Every positive integer reaches 1 under iteration of f.
    ∀ n : ℕ, 0 < n → ∃ k : ℕ, f^[k] n = 1 := by
  sorry

end OMA.S_oeis_a185023
