import OMAReductions.R_wp_unique_games_conjecture_R1_H2_R1_H1_R1

-- Reduction wp-unique-games-conjecture.R1.H2.R1.H1.R1.H2.R1 of step wp-unique-games-conjecture.R1.H2.R1.H1.R1.H2
-- Credit: @my-other-github-account
/-! Adapted from OpenAI, The Unique Games Theorem, 3344da59, MatrixGap and FromMatrixGap.
The intermediate occurrence list need not be simple. A single coordinate system witnesses
binary translations, and repetitions count separately in the 99/100 soundness bound. -/
namespace OMA.R_wp_unique_games_conjecture_R1_H2_R1_H1_R1_H2_R1
open OMA.S_wp_unique_games_conjecture
def H1 : Prop :=
  let Table := (n : ℕ) × {r : List (Fin n × Fin n × Fin n × Bool) // r ≠ []}
  let bits := fun t : Table => ([t.1, t.2.val.length] ++ t.2.val.flatMap fun e =>
    [e.1.val, e.2.1.val, e.2.2.1.val, if e.2.2.2 then 1 else 0]).flatMap fun n => List.replicate n true ++ [false]
  let distinct := fun t : Table => ∀ e ∈ t.2.val, e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2.1 ∧ e.2.1 ≠ e.2.2.1
  let success := fun (t : Table) (a : Fin t.1 → Bool) =>
    (t.2.val.countP (fun e => (xor (xor (a e.1) (a e.2.1)) (a e.2.2.1)) == e.2.2.2) : ℚ) / t.2.val.length
  let Mat := fun q : ℕ => (n : ℕ) × {es : List (Fin n × Fin n × Equiv.Perm (Fin q)) // es ≠ []}
  let mb := fun {q} (G : Mat q) => ([G.1,q,G.2.val.length] ++ G.2.val.flatMap fun e =>
    [e.1.val,e.2.1.val] ++ (List.finRange q).map fun i => (e.2.2 i).val).flatMap unary
  let frac := fun {q} (G : Mat q) (a : Fin G.1 → Fin q) =>
    (G.2.val.countP (fun e => decide (a e.2.1 = e.2.2 (a e.1))) : ℝ) / G.2.val.length
  let trans := fun {q s : ℕ} (c : Fin q ≃ (Fin s → ZMod 2)) (G : Mat q) =>
    ∀ e ∈ G.2.val, ∃ v, ∀ i, c (e.2.2 i) = c i + v
  ∀ d : ℚ, 0 < d → ∃ ξ : ℚ, 0 < ξ ∧ ξ < 1/100 ∧
    ∃ (q s : ℕ) (_ : 2 ≤ q) (_ : 1 ≤ s) (c : Fin q ≃ (Fin s → ZMod 2)) (f : Table → Mat q),
    PolyTime bits mb f ∧ (∀ t, trans c (f t)) ∧ ∀ t, distinct t →
      ((∃ a, 1-ξ ≤ success t a) → ∃ a, 1-(d:ℝ) ≤ frac (f t) a) ∧
      ((∀ a, success t a ≤ 4/5) → ∀ a, frac (f t) a ≤ 99/100)

def H2 : Prop :=
  let Mat := fun q : ℕ => (n : ℕ) × {es : List (Fin n × Fin n × Equiv.Perm (Fin q)) // es ≠ []}
  let mb := fun {q} (G : Mat q) => ([G.1,q,G.2.val.length] ++ G.2.val.flatMap fun e =>
    [e.1.val,e.2.1.val] ++ (List.finRange q).map fun i => (e.2.2 i).val).flatMap unary
  let frac := fun {q} (G : Mat q) (a : Fin G.1 → Fin q) =>
    (G.2.val.countP (fun e => decide (a e.2.1 = e.2.2 (a e.1))) : ℝ) / G.2.val.length
  let trans := fun {q s : ℕ} (c : Fin q ≃ (Fin s → ZMod 2)) (G : Mat q) =>
    ∀ e ∈ G.2.val, ∃ v, ∀ i, c (e.2.2 i) = c i + v
  ∀ ε δ : ℝ, 0 < ε → ε < 1/2 → 0 < δ → δ < 1/2 → ∃ d : ℚ, 0 < d ∧
    ∀ (q s : ℕ), 2 ≤ q → 1 ≤ s → ∀ c : Fin q ≃ (Fin s → ZMod 2),
    ∃ (k : ℕ) (g : {G : Mat q // trans c G} → Instance k), PolyTime (fun z => mb z.val) Instance.bits g ∧
    ∀ z, ((∃ a, 1-(d:ℝ) ≤ frac z.val a) → ∃ a, 1-δ ≤ (g z).fraction a) ∧
      ((∀ a, frac z.val a ≤ 99/100) → ∀ a, (g z).fraction a ≤ ε)

theorem main : H1 → H2 → OMA.R_wp_unique_games_conjecture_R1_H2_R1_H1_R1.H2 := by
  intro A B ε δ hε hε' hδ hδ'
  obtain ⟨d,hd,B⟩ := B ε δ hε hε' hδ hδ'
  obtain ⟨ξ,hξ,hξ',q,s,hq,hs,c,f,⟨m,hm⟩,tr,hf⟩ := A d hd
  obtain ⟨k,g,hg,h⟩ := B q s hq hs c
  let lift := fun t => (⟨f t,tr t⟩ : {G // ∀ e ∈ G.2.val, ∃ v, ∀ i, c (e.2.2 i) = c i + v})
  refine ⟨ξ,hξ,hξ',k,g ∘ lift,OMA.R_wp_unique_games_conjecture_R1.polyTime_comp (f := lift) ⟨{m with outputsFun := m.outputsFun},hm⟩ hg, fun t ht => ?_⟩
  exact ⟨(h _).1 ∘ (hf t ht).1, (h _).2 ∘ (hf t ht).2⟩
end OMA.R_wp_unique_games_conjecture_R1_H2_R1_H1_R1_H2_R1
