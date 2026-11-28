import Mathlib

/-!
# Refuting random 3SAT-instances on O(n) clauses (weak form)

Source: https://www.openproblemgarden.org/op/refuting_random_3sat_instances_on_o_n_clauses_weak_form
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Feige): for every rational `ε > 0` and every rational `Δ` there is no polynomial-time
algorithm which, given a 3CNF formula `I` on `n` variables with `m = ⌊Δ n⌋` clauses drawn
uniformly at random, returns "typical" with probability at least `1/2`, while never returning
"typical" on an instance with at least `(1 - ε) m` simultaneously satisfiable clauses.

Conventions:
* An instance on `n` variables with `m` clauses is `I : Fin m → Fin 3 → Fin n × Bool`; a literal
  `(v, s)` is satisfied by `a : Fin n → Bool` when `a v = s`. Clauses are drawn independently and
  uniformly, with replacement, as ordered triples of literals (the source notes that such
  choices of the uniform distribution do not affect the truth of the weak form).
* Algorithms are deterministic polynomial-time Turing machines (Mathlib's
  `Turing.TM2ComputableInPolyTime`) reading a binary encoding of `(n, I)` and returning a bit
  (`true` = "typical").
* "With probability at least 0.5" is required for all sufficiently large `n` (Feige's
  formulation); the soundness condition is required on every instance.
-/

namespace OMA.S_opg_refuting_random_3sat_instances_on_o_n_clauses_weak_form

/-- Self-delimiting binary encoding of a natural number. -/
def encNat (k : ℕ) : List Bool := (Nat.bits k).flatMap (fun b => [true, b]) ++ [false, false]

/-- Binary encoding of an instance on `n` variables. -/
def encInst {n m : ℕ} (I : Fin m → Fin 3 → Fin n × Bool) : List Bool :=
  encNat n ++ encNat m ++
    (List.finRange m).flatMap (fun j =>
      (List.finRange 3).flatMap (fun k => (I j k).2 :: encNat (I j k).1))

/-- Number of clauses of `I` satisfied by the assignment `a`. -/
def numSat {n m : ℕ} (I : Fin m → Fin 3 → Fin n × Bool) (a : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => ∃ k : Fin 3, a (I j k).1 = (I j k).2)).card

theorem main :
    ∀ ε Δ : ℚ, 0 < ε →
      ¬ ∃ f : List Bool → Bool,
        Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
          (fun b : Bool => [b]) f) ∧
        -- never "typical" on an instance with `(1 - ε) m` simultaneously satisfiable clauses
        (∀ (n : ℕ) (I : Fin (⌊Δ * n⌋.toNat) → Fin 3 → Fin n × Bool),
          (∃ a : Fin n → Bool, (1 - ε) * (⌊Δ * n⌋.toNat : ℚ) ≤ numSat I a) →
            f (encInst I) = false) ∧
        -- "typical" with probability at least 1/2 on random instances, `m = ⌊Δ n⌋`
        (∀ᶠ n : ℕ in Filter.atTop,
          (1 / 2 : ℚ) * (Fintype.card (Fin (⌊Δ * n⌋.toNat) → Fin 3 → Fin n × Bool) : ℚ) ≤
            ((Finset.univ.filter (fun I : Fin (⌊Δ * n⌋.toNat) → Fin 3 → Fin n × Bool =>
              f (encInst I) = true)).card : ℚ)) := by
  sorry

end OMA.S_opg_refuting_random_3sat_instances_on_o_n_clauses_weak_form
