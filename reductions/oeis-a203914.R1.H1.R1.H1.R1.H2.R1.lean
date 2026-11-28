import OMAReductions.R_oeis_a203914_R1_H1_R1_H1_R1
/- Binary 3SAT to simple bipartite Unique Games, then long-code MaxCut testing.
Adapted from OpenAI math 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OMA.R_oeis_a203914_R1_H1_R1_H1_R1_H2_R1
open OMA.S_oeis_a203914 Turing

def H1 : Prop :=
  let L := fun w : List Bool => ∃ (cs : List (Fin 3 → ℕ × Bool)) (v : ℕ → Bool),
      w = cs.flatMap (fun c => true :: (List.finRange 3).flatMap (fun i => (c i).2 :: natBits (c i).1)) ++ [false] ∧
      ∀ c ∈ cs, ∃ i, v (c i).1 = (c i).2
  ∀ ε δ : ℝ, 0 < ε → ε < 1/2 → 0 < δ → δ < 1/2 → ∃ (q : ℕ) (_ : 2 ≤ q), let I := Σ n : ℕ, List (Fin n × Fin n × Equiv.Perm (Fin q))
    ∃ f : List Bool → I,
      Nonempty (TM2ComputableInPolyTime id (fun p : I =>
        ([p.1,q,p.2.length] ++ p.2.flatMap (fun (u,v,π) => [u.val,v.val] ++ (List.finRange q).map (fun i => (π i).val))).flatMap (fun n => List.replicate n true ++ [false])) f) ∧
      ∀ w, let es := (f w).2
           let score := fun (l : Fin (f w).1 → Fin q) => ((es.filter (fun (u,v,π) => decide (π (l u) = l v))).length : ℝ) / es.length
           es ≠ [] ∧ (es.map (fun e => (e.1,e.2.1))).Nodup ∧
           (∃ side : Fin (f w).1 → Bool, ∀ e ∈ es, side e.1 = false ∧ side e.2.1 = true) ∧
           (L w → ∃ l, 1 - ε ≤ score l) ∧ (¬ L w → ∀ l, score l ≤ δ)

def H2 : Prop :=
  ∀ α : ℝ, alphaGW < α → α ≤ 1 → ∃ ε δ : ℝ, 0 < ε ∧ ε < 1/2 ∧ 0 < δ ∧ δ < 1/2 ∧
  ∀ L : List Bool → Prop, (∃ (q : ℕ) (_ : 2 ≤ q), let I := Σ n : ℕ, List (Fin n × Fin n × Equiv.Perm (Fin q))
    ∃ f : List Bool → I,
      Nonempty (TM2ComputableInPolyTime id (fun p : I =>
        ([p.1,q,p.2.length] ++ p.2.flatMap (fun (u,v,π) => [u.val,v.val] ++ (List.finRange q).map (fun i => (π i).val))).flatMap (fun n => List.replicate n true ++ [false])) f) ∧
      ∀ w, let es := (f w).2
           let score := fun (l : Fin (f w).1 → Fin q) => ((es.filter (fun (u,v,π) => decide (π (l u) = l v))).length : ℝ) / es.length
           es ≠ [] ∧ (es.map (fun e => (e.1,e.2.1))).Nodup ∧
           (∃ side : Fin (f w).1 → Bool, ∀ e ∈ es, side e.1 = false ∧ side e.2.1 = true) ∧
           (L w → ∃ l, 1 - ε ≤ score l) ∧ (¬ L w → ∀ l, score l ≤ δ)) → ∃ (c s : ℚ) (g : List Bool → ℕ × Σ n : ℕ, SimpleGraph (Fin n)),
    0 < c ∧ 0 ≤ s ∧ (s : ℝ) < α * c ∧
    Nonempty (TM2ComputableInPolyTime id (fun p : ℕ × Σ n : ℕ, SimpleGraph (Fin n) => natBits p.2.1 ++ natBits p.1 ++ graphBits p.2.2) g) ∧
    ∀ w, 0 < (g w).1 ∧ (L w → (c : ℝ) * (g w).1 ≤ (maxCut (g w).2.2 : ℝ)) ∧
           (¬ L w → (maxCut (g w).2.2 : ℝ) ≤ (s : ℝ) * (g w).1)

theorem main : H1 → H2 → OMA.R_oeis_a203914_R1_H1_R1_H1_R1.H2 := by
  intro p t α ha hb
  obtain ⟨ε,δ,he,he',hd,hd',test⟩ := t α ha hb
  exact test _ (p ε δ he he' hd hd')
end OMA.R_oeis_a203914_R1_H1_R1_H1_R1_H2_R1
