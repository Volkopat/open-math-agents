import FormalConjectures.ErdosProblems.«951»

open Filter
open scoped Nat.Prime

-- Reduction of Erdős Problem 951: the Beurling-prime counting bound.
--
-- H1 is the upstream-proved transfer lemma `erdos_951.variants.isBeurlingPrimes`:
-- the target's hypotheses (1 < a 0, StrictMono a, Erdos951Prop a) are exactly
-- the assumptions of that lemma, and its conclusion is `IsBeurlingPrimes a`.
-- H2 isolates the genuinely open core: for a Beurling prime sequence, the
-- counting function #{a i <= x} is eventually bounded by the ordinary prime
-- counting function pi(floor x).  main composes the proved transfer with H2.
-- Neither H is a conjunct of the target and neither is stronger than it.

namespace OMA.R_Erdos951_erdos_951_R1

def H1 : Prop :=
  ∀ a : ℕ → ℝ, 1 < a 0 → StrictMono a → Erdos951.Erdos951Prop a → IsBeurlingPrimes a

def H2 : Prop :=
  ∀ a : ℕ → ℝ, IsBeurlingPrimes a →
    ∀ᶠ x : ℝ in Filter.atTop, {i : ℕ | a i ≤ x}.ncard ≤ π ⌊x⌋₊

theorem main : H1 → H2 → type_of% @Erdos951.erdos_951 := by
  intro h1 h2 a ha hm he
  exact h2 a (h1 a ha hm he)

end OMA.R_Erdos951_erdos_951_R1
