import Mathlib

/-!
# A389335: the three-colour Ramsey number r(C_n, C_n, C_n)

Source: https://oeis.org/A389335
Credit: @rpabani

a(n) is the smallest m such that every red-green-blue edge-colouring of the complete graph K_m
contains a red, green or blue n-cycle.

Conjecture (Bondy and Erdős, as quoted in OEIS A389335): a(n) <= 4n - 3 for n >= 4.

A colouring is a map from unordered pairs of vertices to three colours; its values on the
diagonal pairs are irrelevant, since those are not edges and no walk uses them. An n-cycle is a
closed walk of length n in the complete graph that is a cycle. The set defining a(n) is nonempty
for n >= 3 by Ramsey's theorem, so the infimum is a minimum, as in the source.
-/

namespace OMA.S_oeis_a389335

/-- Every colouring of the edges of `K_m` with three colours has a monochromatic `n`-cycle. -/
def ForcesMonoCycle (n m : ℕ) : Prop :=
  ∀ c : Sym2 (Fin m) → Fin 3,
    ∃ (i : Fin 3) (v : Fin m) (w : (⊤ : SimpleGraph (Fin m)).Walk v v),
      w.IsCycle ∧ w.length = n ∧ ∀ e ∈ w.edges, c e = i

/-- `a n` is the Ramsey number r(C_n, C_n, C_n) (OEIS A389335). -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | ForcesMonoCycle n m}

theorem main : ∀ n : ℕ, 4 ≤ n → a n ≤ 4 * n - 3 := by
  sorry

end OMA.S_oeis_a389335
