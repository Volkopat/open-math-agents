import OMAReductions.R_Erdos1135_erdos_1135_R2_H1_R1

-- Reduction Erdos1135.erdos_1135.R2.H1.R1.H1.R1 of step Erdos1135.erdos_1135.R2.H1.R1.H1
-- Credit: @arindale
--
-- The open dynamical hypothesis is "every n ≡ 3 (mod 4) above 2048 has a descending
-- iterate under the accelerated Collatz map T".  The two residue classes mod 8 in
-- that congruence class behave differently at the first accelerated step:
--   n ≡ 3 (mod 8)  ->  T n ≡ 1 (mod 4) is odd and T^3 n = (9 n + 5) / 8,
--   n ≡ 7 (mod 8)  ->  T n ≡ 3 (mod 4) stays in the same class.
-- Splitting by these two classes gives two independent stopping-time targets, and
-- the combination is the elementary residue case split (n mod 4 = 3 forces
-- n mod 8 ∈ {3, 7}).

namespace OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1

/-- Stopping time for the class `n ≡ 3 (mod 8)`: the first accelerated step lands in
the `≡ 1 (mod 4)` odd class. -/
def H1 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 8 = 3 → ∃ k : ℕ, T^[k] n < n

/-- Stopping time for the class `n ≡ 7 (mod 8)`: the first accelerated step stays in
the odd `≡ 3 (mod 4)` class. -/
def H2 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 8 = 7 → ∃ k : ℕ, T^[k] n < n

theorem main : H1 → H2 → OMA.R_Erdos1135_erdos_1135_R2_H1_R1.H1 := by
  intro h1 h2
  dsimp only [OMA.R_Erdos1135_erdos_1135_R2_H1_R1.H1]
  intro n hn hmod
  have h8 : n % 8 = 3 ∨ n % 8 = 7 := by omega
  rcases h8 with h | h
  · exact h1 n hn h
  · exact h2 n hn h

end OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1
