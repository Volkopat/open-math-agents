import OMAReductions.R_oeis_a203914_R1_H1_R1

/-! Binary 3SAT separates Cook–Levin, the OpenAI MaxCut gap theorem
(math 3344da59991ed94f9ba711217b29c1d760badfa6), and TM2 composition.
The literal sign precedes the canonical delimited variable name. -/
namespace OMA.R_oeis_a203914_R1_H1_R1_H1_R1
open OMA.S_oeis_a203914 Turing

def H1 : Prop :=
  ∀ L ∈ NP, ∃ f : List Bool → List Bool, Nonempty (TM2ComputableInPolyTime id id f) ∧
    ∀ x, L x = true ↔ (let w := f x; (∃ (cs : List (Fin 3 → ℕ × Bool)) (v : ℕ → Bool),
      w = cs.flatMap (fun c => true :: (List.finRange 3).flatMap (fun i => (c i).2 :: natBits (c i).1)) ++ [false] ∧
      ∀ c ∈ cs, ∃ i, v (c i).1 = (c i).2))

def H2 : Prop :=
  ∀ α : ℝ, alphaGW < α → α ≤ 1 → ∃ (c s : ℚ) (g : List Bool → ℕ × Σ n : ℕ, SimpleGraph (Fin n)),
    0 < c ∧ 0 ≤ s ∧ (s : ℝ) < α * c ∧
    Nonempty (TM2ComputableInPolyTime id (fun p : ℕ × Σ n : ℕ, SimpleGraph (Fin n) => natBits p.2.1 ++ natBits p.1 ++ graphBits p.2.2) g) ∧
    ∀ w, let sat := (∃ (cs : List (Fin 3 → ℕ × Bool)) (v : ℕ → Bool),
      w = cs.flatMap (fun c => true :: (List.finRange 3).flatMap (fun i => (c i).2 :: natBits (c i).1)) ++ [false] ∧
      ∀ c ∈ cs, ∃ i, v (c i).1 = (c i).2)
         0 < (g w).1 ∧ (sat → (c : ℝ) * (g w).1 ≤ (maxCut (g w).2.2 : ℝ)) ∧
           (¬ sat → (maxCut (g w).2.2 : ℝ) ≤ (s : ℝ) * (g w).1)

def H3 : Prop :=
  ∀ (Y : Type) (enc : Y → List Bool) (f : List Bool → List Bool) (g : List Bool → Y),
    Nonempty (TM2ComputableInPolyTime id id f) → Nonempty (TM2ComputableInPolyTime id enc g) →
    Nonempty (TM2ComputableInPolyTime id enc (fun x => g (f x)))

theorem main : H1 → H2 → H3 → OMA.R_oeis_a203914_R1_H1_R1.H1 := by
  intro cook gap comp α ha h1 L hL
  obtain ⟨f, hf, he⟩ := cook L hL
  obtain ⟨c,s,g,hc,hs,hgap,hg,hw⟩ := gap α ha h1
  refine ⟨c,s,fun x => g (f x),hc,hs,hgap,comp _ _ _ _ hf hg,?_⟩
  intro x
  obtain ⟨hp,hy,hn⟩ := hw (f x)
  exact ⟨hp, fun hx => hy ((he x).mp hx), fun hx => hn (fun h => by simpa [hx] using (he x).mpr h)⟩
end OMA.R_oeis_a203914_R1_H1_R1_H1_R1
