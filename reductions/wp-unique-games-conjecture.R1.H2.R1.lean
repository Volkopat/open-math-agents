import OMAReductions.R_wp_unique_games_conjecture_R1

-- Reduction wp-unique-games-conjecture.R1.H2.R1 of step wp-unique-games-conjecture.R1.H2
-- Credit: @my-other-github-account

/-!
# Split 3-Coloring-to-Gap-Unique-Games through binary 3SAT

Both hypotheses pass through the language of canonically encoded three-slot formulas.
A clause is three literals; a literal is a variable name `m` and a sign `s`. It is written as
`s`, then each bit of `Nat.bits m` (least significant first) preceded by `true`, then `false`.
A clause is `true` followed by its three literals, and the formula ends with `false`. A formula
is satisfied by `a : ℕ → Bool` when every clause has a literal with `a m = s`.

This is exactly the binary 3SAT language `BinaryLanguage.language` of the Lean development of
OpenAI, The Unique Games Theorem (2026), https://github.com/openai/math
(lean/ComparatorChallenges/UniqueGamesTheorem.lean at commit
3344da59991ed94f9ba711217b29c1d760badfa6): its decoder accepts precisely these canonical
strings, which is why the language is spelled out here by its encoder.

* `H1` is that development's Unique Games Theorem (`OAI.UniqueGamesTheorem.theorem11`) in the
  instance encoding of `OMA.S_wp_unique_games_conjecture`: for all small `ε, δ > 0`, binary 3SAT
  reduces in polynomial time, with finite stack alphabets, to the `(1 - δ, ε)` gap problem for
  unique label cover with `k` colors.
* `H2` is Karp's reduction from 3-Coloring of `n * n` adjacency-matrix bit strings to binary 3SAT.

`main` composes them with `polyTime_comp` from the parent reduction.
-/

namespace OMA.R_wp_unique_games_conjecture_R1_H2_R1

/-- The Unique Games Theorem for binary 3SAT, in the encoding of the statement. -/
def H1 : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < ε₀ →
      ∃ (k : ℕ) (g : List Bool → OMA.S_wp_unique_games_conjecture.Instance k),
        OMA.S_wp_unique_games_conjecture.PolyTime id
          OMA.S_wp_unique_games_conjecture.Instance.bits g ∧
        ∀ x : List Bool,
          ((∃ cs : List (Fin 3 → ℕ × Bool),
          x = (cs.flatMap fun c => true :: (List.finRange 3).flatMap fun t =>
            (c t).2 :: ((c t).1.bits.flatMap fun b => [true, b]) ++ [false]) ++ [false] ∧
          ∃ a : ℕ → Bool, ∀ c ∈ cs, ∃ t, a (c t).1 = (c t).2) → ∃ a, 1 - δ ≤ (g x).fraction a) ∧
          (¬ (∃ cs : List (Fin 3 → ℕ × Bool),
          x = (cs.flatMap fun c => true :: (List.finRange 3).flatMap fun t =>
            (c t).2 :: ((c t).1.bits.flatMap fun b => [true, b]) ++ [false]) ++ [false] ∧
          ∃ a : ℕ → Bool, ∀ c ∈ cs, ∃ t, a (c t).1 = (c t).2) → ∀ a, (g x).fraction a ≤ ε)

/-- 3-Coloring of square adjacency matrices reduces in polynomial time to binary 3SAT. -/
def H2 : Prop :=
  ∃ f : List Bool → List Bool, OMA.S_wp_unique_games_conjecture.PolyTime id id f ∧
    ∀ y : List Bool, (∃ cs : List (Fin 3 → ℕ × Bool),
          f y = (cs.flatMap fun c => true :: (List.finRange 3).flatMap fun t =>
            (c t).2 :: ((c t).1.bits.flatMap fun b => [true, b]) ++ [false]) ++ [false] ∧
          ∃ a : ℕ → Bool, ∀ c ∈ cs, ∃ t, a (c t).1 = (c t).2) ↔
      ∃ (n : ℕ) (c : Fin n → Fin 3), y.length = n * n ∧
        ∀ i j : Fin n, y.getD (i.val * n + j.val) false = true → c i ≠ c j

theorem main : H1 → H2 → OMA.R_wp_unique_games_conjecture_R1.H2 := by
  rintro ⟨ε₀, hε₀, h1⟩ ⟨f, hf, hfl⟩
  refine ⟨ε₀, hε₀, fun ε δ hε hε' hδ hδ' => ?_⟩
  obtain ⟨k, g, hg, hgap⟩ := h1 ε δ hε hε' hδ hδ'
  refine ⟨k, g ∘ f, OMA.R_wp_unique_games_conjecture_R1.polyTime_comp hf hg,
    fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · exact (hgap (f y)).1 ((hfl y).2 hy)
  · exact (hgap (f y)).2 (fun h => hy ((hfl y).1 h))

end OMA.R_wp_unique_games_conjecture_R1_H2_R1
