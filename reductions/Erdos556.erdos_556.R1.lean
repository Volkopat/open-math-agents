import FormalConjectures.ErdosProblems.«556»

-- Reduction Erdos556.erdos_556.R1 of Erdős Problem 556
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Split by the length n of the cycle (the bound is R(C_n; 3) ≤ 4n - 3 for n ≥ 4):
-- * H1, n = 4: every 3-colouring of the edges of K_13 has a monochromatic C_4. This has an
--   elementary proof (Bialostocki–Schönheim style double counting): in a C_4-free colour two
--   vertices share at most one neighbour, so the sum of d(d-1) over vertices is at most 13·12 per
--   colour, while the three degrees at a vertex sum to 12, forcing every colour to be 4-regular
--   with every pair having exactly one common neighbour; then the edges split into triangles,
--   but 26 edges is not a multiple of 3. A Lean proof of H1 is ready and will be sent as a step.
-- * H2, 5 ≤ n ≤ 8: the known small values R(C_5;3) = 17, R(C_6;3) = 12, R(C_7;3) = 25,
--   R(C_8;3) = 16 (Radziszowski, Small Ramsey Numbers, DS1, Table XII), all ≤ 4n - 3; a finite
--   but large computation (or the computer-free proof of Faudree–Schelten–Schiermeyer for n = 7).
-- * H3, n ≥ 9: the genuinely open range (R(C_9;3) ≤ 33 is the first unknown case); known for
--   large n by Kohayakawa–Simonovits–Skokan / Jenssen–Skokan (odd) and Benevides–Skokan (even).

namespace OMA.R_Erdos556_erdos_556_R1

open SimpleGraph

/-- n = 4: every 3-colouring of the edges of K_13 contains a monochromatic 4-cycle. -/
def H1 : Prop :=
  ∀ c : Fin 3 → SimpleGraph (Fin 13),
    (⊤ : SimpleGraph (Fin 13)).IsEdgeColouring c → ∃ i, cycleGraph 4 ⊑ c i

/-- 5 ≤ n ≤ 8: the known small cases. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 ≤ n → n ≤ 8 →
    ∀ c : Fin 3 → SimpleGraph (Fin (4 * n - 3)),
      (⊤ : SimpleGraph (Fin (4 * n - 3))).IsEdgeColouring c → ∃ i, cycleGraph n ⊑ c i

/-- n ≥ 9: the open range. -/
def H3 : Prop :=
  ∀ n : ℕ, 9 ≤ n →
    ∀ c : Fin 3 → SimpleGraph (Fin (4 * n - 3)),
      (⊤ : SimpleGraph (Fin (4 * n - 3))).IsEdgeColouring c → ∃ i, cycleGraph n ⊑ c i

theorem main : H1 → H2 → H3 → type_of% @Erdos556.erdos_556 := by
  intro h1 h2 h3 n hn
  unfold multicolourRamsey
  apply Nat.sInf_le
  rcases Nat.lt_or_ge n 9 with h | h
  · rcases Nat.lt_or_ge n 5 with h' | h'
    · have : n = 4 := by omega
      subst this
      exact h1
    · exact h2 n h' (by omega)
  · exact h3 n h

end OMA.R_Erdos556_erdos_556_R1
