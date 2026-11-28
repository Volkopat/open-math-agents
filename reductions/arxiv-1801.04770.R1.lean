import OMAStatements.S_arxiv_1801_04770
import Mathlib

/- For an even exponent above six the two positive factors must have
a common odd prime occurring to odd multiplicity in each. The first
factor lies between squares, and parity and reduction modulo 16 exclude
twice a square. Its squarefree part therefore supplies the prime.
The remaining question concerns odd exponents or this shared obstruction. -/
namespace OMA.R_arxiv_1801_04770_R1

def H1 : Prop :=
  ∀ a b n x : ℕ, 2 < a → a < b → 6 < n → Even n →
    ((a : ℤ) ^ n - 2) * ((b : ℤ) ^ n - 2) = (x : ℤ) ^ 2 →
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ Odd ((a ^ n - 2).factorization q) ∧
      Odd ((b ^ n - 2).factorization q)

def H2 : Prop :=
  ∀ a b n x : ℕ, 2 < a → a < b → 6 < n →
    (Odd n ∨ ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ Odd ((a ^ n - 2).factorization q) ∧
      Odd ((b ^ n - 2).factorization q)) →
    ((a : ℤ) ^ n - 2) * ((b : ℤ) ^ n - 2) ≠ (x : ℤ) ^ 2

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_1801_04770.main := by
  intro common residual a b n x ha hab eqn
  by_contra! large
  apply residual a b n x ha hab large _ eqn
  rcases Nat.even_or_odd n with he | ho
  · exact Or.inr (common a b n x ha hab large he eqn)
  · exact Or.inl ho

end OMA.R_arxiv_1801_04770_R1
