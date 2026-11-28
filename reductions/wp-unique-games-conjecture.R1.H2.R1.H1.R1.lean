import OMAReductions.R_wp_unique_games_conjecture_R1_H2_R1

-- Reduction wp-unique-games-conjecture.R1.H2.R1.H1.R1 of step wp-unique-games-conjecture.R1.H2.R1.H1
-- Credit: @my-other-github-account
/-! Factor the reduction through near-satisfiable ternary parity systems on distinct names.
Adapted from OpenAI, The Unique Games Theorem, commit 3344da59991ed94f9ba711217b29c1d760badfa6,
BinaryParityReduction and FromMatrixGap. Multiplicities are retained in the occurrence list. -/
namespace OMA.R_wp_unique_games_conjecture_R1_H2_R1_H1_R1
open OMA.S_wp_unique_games_conjecture
def H1 : Prop :=
  let Table := (n : ℕ) × {r : List (Fin n × Fin n × Fin n × Bool) // r ≠ []}
  let bits := fun t : Table => ([t.1, t.2.val.length] ++ t.2.val.flatMap fun e =>
    [e.1.val, e.2.1.val, e.2.2.1.val, if e.2.2.2 then 1 else 0]).flatMap fun n => List.replicate n true ++ [false]
  let distinct := fun t : Table => ∀ e ∈ t.2.val, e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2.1 ∧ e.2.1 ≠ e.2.2.1
  let success := fun (t : Table) (a : Fin t.1 → Bool) =>
    (t.2.val.countP (fun e => (xor (xor (a e.1) (a e.2.1)) (a e.2.2.1)) == e.2.2.2) : ℚ) / t.2.val.length
  let Sat3 := fun x : List Bool => ∃ cs : List (Fin 3 → ℕ × Bool),
    x = (cs.flatMap fun c => true :: (List.finRange 3).flatMap fun t =>
      (c t).2 :: ((c t).1.bits.flatMap fun b => [true, b]) ++ [false]) ++ [false] ∧
    ∃ a : ℕ → Bool, ∀ c ∈ cs, ∃ t, a (c t).1 = (c t).2
  ∀ ξ : ℚ, 0 < ξ → ξ < 1/100 → ∃ f : List Bool → Table,
  PolyTime id bits f ∧ ∀ x, distinct (f x) ∧
    (Sat3 x → ∃ a, 1-ξ ≤ success (f x) a) ∧ (¬Sat3 x → ∀ a, success (f x) a ≤ 4/5)

def H2 : Prop :=
  let Table := (n : ℕ) × {r : List (Fin n × Fin n × Fin n × Bool) // r ≠ []}
  let bits := fun t : Table => ([t.1, t.2.val.length] ++ t.2.val.flatMap fun e =>
    [e.1.val, e.2.1.val, e.2.2.1.val, if e.2.2.2 then 1 else 0]).flatMap fun n => List.replicate n true ++ [false]
  let distinct := fun t : Table => ∀ e ∈ t.2.val, e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2.1 ∧ e.2.1 ≠ e.2.2.1
  let success := fun (t : Table) (a : Fin t.1 → Bool) =>
    (t.2.val.countP (fun e => (xor (xor (a e.1) (a e.2.1)) (a e.2.2.1)) == e.2.2.2) : ℚ) / t.2.val.length
  ∀ ε δ : ℝ, 0 < ε → ε < 1/2 → 0 < δ → δ < 1/2 →
  ∃ ξ : ℚ, 0 < ξ ∧ ξ < 1/100 ∧ ∃ (k : ℕ) (g : Table → Instance k),
  PolyTime bits Instance.bits g ∧ ∀ t, distinct t →
    ((∃ a, 1-ξ ≤ success t a) → ∃ a, 1-δ ≤ (g t).fraction a) ∧
    ((∀ a, success t a ≤ 4/5) → ∀ a, (g t).fraction a ≤ ε)

theorem main : H1 → H2 → OMA.R_wp_unique_games_conjecture_R1_H2_R1.H1 := by
  intro p q
  refine ⟨1/2, by norm_num, fun ε δ hε hε' hδ hδ' => ?_⟩
  obtain ⟨ξ, hξ, hξ', k, g, hg, h⟩ := q ε δ hε hε' hδ hδ'
  obtain ⟨f, hf, h'⟩ := p ξ hξ hξ'
  refine ⟨k, g ∘ f, OMA.R_wp_unique_games_conjecture_R1.polyTime_comp hf hg, fun x => ?_⟩
  exact ⟨(h _ (h' x).1).1 ∘ (h' x).2.1, (h _ (h' x).1).2 ∘ (h' x).2.2⟩
end OMA.R_wp_unique_games_conjecture_R1_H2_R1_H1_R1
