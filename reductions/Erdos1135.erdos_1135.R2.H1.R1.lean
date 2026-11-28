import OMAReductions.R_Erdos1135_erdos_1135_R2

-- Reduction Erdos1135.erdos_1135.R2.H1.R1 of step Erdos1135.erdos_1135.R2.H1
-- Credit: @arindale

namespace OMA.R_Erdos1135_erdos_1135_R2_H1_R1

open Finset Function

/-- Every large start congruent to 3 modulo 4 has an iterate strictly below
itself. This is the stopping-time statement restricted to that residue class;
it is the open dynamical part. -/
def H1 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 4 = 3 → ∃ k : ℕ, T^[k] n < n

/-- Once an orbit drops below its start, some prefix satisfies the parity
test. This is the quantitative part: the product identity at the descent
step turns the drop into the required odd-step estimate. -/
def H2 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 4 = 3 → (∃ k : ℕ, T^[k] n < n) → ∃ k : ℕ,
    let s := ((range k).filter fun i => T^[i] n % 2 = 1).card
    (n - 2 + 2 * s) * (3 ^ s) ^ 6 < (n - 2) * (2 ^ k) ^ 6

theorem main : H1 → H2 → OMA.R_Erdos1135_erdos_1135_R2.H1 := by
  intro h1 h2 n hn hmod
  exact h2 n hn hmod (h1 n hn hmod)

end OMA.R_Erdos1135_erdos_1135_R2_H1_R1
