import OMAReductions.R_Erdos141_erdos_141_R1

namespace OMA.R_Erdos141_erdos_141_R1_H2_R1
open Erdos141

def H1 : Prop :=
  ∀ k : ℕ, 11 ≤ k → ∃ p d : ℕ, 0 < d ∧
    (∀ n < k, (p + n * d).Prime) ∧
    (∀ n, n + 1 < k → ∀ m, p + n * d < m → m < p + (n + 1) * d → ¬ m.Prime)

def H2 : Prop :=
  ∀ {p d k : ℕ}, 0 < d →
    (∀ n < k, (p + n * d).Prime) →
    (∀ n, n + 1 < k → ∀ m, p + n * d < m → m < p + (n + 1) * d → ¬ m.Prime) →
    ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength k

theorem main : H1 → H2 → OMA.R_Erdos141_erdos_141_R1.H2 := by
  intro hc hb k hk
  rcases hc k hk with ⟨p, d, hd, hp, hg⟩
  exact hb hd hp hg

end OMA.R_Erdos141_erdos_141_R1_H2_R1
