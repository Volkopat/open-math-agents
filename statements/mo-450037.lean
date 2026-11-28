import Mathlib

/-!
# Independence of squarefree products of homogeneous polynomials

Source: Lchencz, https://mathoverflow.net/questions/450037 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)

The first condition uses the rank of a table of ordinary evaluations of the
original polynomials. For squares of real linear forms the second condition
only requires the pairwise dot products of their coefficient vectors.
Both tests include dependent inputs as well as the independent families in
the question.
-/

namespace OMA.S_mo_450037

abbrev Subsets (n k : ℕ) := {S : Finset (Fin n) // S.card=k}
abbrev Pairs (n : ℕ) := {s : Fin n × Fin n // s.1 < s.2}

noncomputable def valueTable {K : Type*} [Field K] {m n k d : ℕ}
    (F : Fin n → MvPolynomial (Fin m) K) (grid : Fin (k*d+1) → K) :
    Matrix (Fin m → Fin (k*d+1)) (Subsets n k) K := Matrix.of fun x S =>
  ∏ i ∈ S.1, MvPolynomial.eval (fun j => grid (x j)) (F i)

noncomputable def form {m : ℕ} (u : Fin m → ℝ) : MvPolynomial (Fin m) ℝ :=
  ∑ j, MvPolynomial.C (u j)*MvPolynomial.X j

noncomputable def pairMatrix {m n : ℕ} (u : Fin n → Fin m → ℝ) : Matrix (Pairs n) (Pairs n) ℝ :=
  Matrix.of fun e f =>
    let g i j := dotProduct (u i) (u j)
    let i := e.1.1
    let j := e.1.2
    let k := f.1.1
    let l := f.1.2
    (g i k)^2*(g j l)^2+4*g i k*g i l*g j k*g j l+(g i l)^2*(g j k)^2

theorem main :
    (∀ (K : Type) [Field K] (m n k d : ℕ) (F : Fin n → MvPolynomial (Fin m) K)
      (grid : Fin (k*d+1) → K), Function.Injective grid → (∀ i, (F i).IsHomogeneous d) →
      (LinearIndependent K (fun S : Subsets n k => ∏ i ∈ S.1, F i) ↔
        (valueTable F grid).rank = Fintype.card (Subsets n k))) ∧
    (∀ (m n : ℕ) (u : Fin n → Fin m → ℝ),
      LinearIndependent ℝ (fun s : Pairs n => form (u s.1.1)^2*form (u s.1.2)^2) ↔
        (pairMatrix u).det ≠ 0) := by
  sorry

end OMA.S_mo_450037
