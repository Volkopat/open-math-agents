import Mathlib

/-!
# A signed subset ratio at fixed cardinality

Source: Anson, https://mathoverflow.net/questions/453796 (CC BY-SA).
icecuber gave a reduction from PARTITION. Credit: @connoranderson.
Here the weights and the decision threshold are integers. When any feasible
numerator is nonnegative, one can instead scan finitely many linear scores.
-/
namespace OMA.S_mo_453796
open Finset
noncomputable def ratio {ι} (a b : ι→ℝ) (S : Finset ι) : ℝ :=
  (∑ i∈S,a i)/Real.sqrt (∑ i∈S,b i)
def size {n} (u : Fin n→ℕ) : ℕ := n*(1+∑ i,u i)
def β {n} (u : Fin n→ℕ) (i : Fin n⊕Fin n) : ℕ :=
  size u * (1+2*n*(Sum.elim u (fun _ => 0) i))
def α {n} (u : Fin n→ℕ) (i : Fin n⊕Fin n) : ℤ :=
  -(β u i : ℤ) - (n:ℤ)*(1+(∑ j,u j : ℕ))^2
def score {n} (a b : Fin n→ℝ) (t : ℝ) (i : Fin n) : ℝ := a i-t*b i
def Top {n} (k : ℕ) (f : Fin n→ℝ) (S : Finset (Fin n)) : Prop :=
  S.card=k ∧ ∀ i∈S, ∀ j∉S, f j≤f i
noncomputable def breaks {n} (a b : Fin n→ℝ) : Finset ℝ := by
  classical
  exact insert 0 (univ.image (fun p : Fin n × Fin n => (a p.1-a p.2)/(b p.1-b p.2)))
noncomputable def samples {n} (a b : Fin n→ℝ) : Finset ℝ := by
  classical
  let E:=breaks a b
  exact E ∪ E.image (fun x => x+1) ∪ (E ×ˢ E).image (fun p => (p.1+p.2)/2)

theorem main :
    (∀ (n : ℕ) (u : Fin n→ℕ), 0<n →
      (∀ i,α u i<0 ∧ 0<β u i) ∧
      (∀ S : Finset (Fin n⊕Fin n), S.card=n →
        ratio (fun i => (α u i:ℝ)) (fun i => (β u i:ℝ)) S ≤ -2*(size u:ℝ)) ∧
      ((∃ T : Finset (Fin n), 2*(∑ i∈T,u i)=∑ i,u i) ↔
        ∃ S : Finset (Fin n⊕Fin n), S.card=n ∧
          ratio (fun i => (α u i:ℝ)) (fun i => (β u i:ℝ)) S = -2*(size u:ℝ))) ∧
    (∀ n k : ℕ, ((univ : Finset (Fin n)).powersetCard k).card=n.choose k ∧ n.choose k≤n^k) ∧
    (∀ (n k : ℕ) (a b : Fin n→ℝ), 0<k → k≤n → (∀ i,0<b i) →
      (∃ S : Finset (Fin n), S.card=k ∧ 0≤∑ i∈S,a i) →
      (samples a b).card ≤ 2*(n^2+1)+(n^2+1)^2 ∧
      (∃ choose : ℝ→Finset (Fin n), ∀ t,Top k (score a b t) (choose t)) ∧
      ∀ choose : ℝ→Finset (Fin n), (∀ t,Top k (score a b t) (choose t)) →
        ∃ t∈samples a b, ∀ S : Finset (Fin n), S.card=k →
          ratio a b S ≤ ratio a b (choose t)) := by
  sorry
end OMA.S_mo_453796
