import Mathlib

/-!
# Fibonacci totients and Sophie Germain primes: the converse conjecture

Aradhya Goel, Sophie Germain Primes and the Totient of Fibonacci Numbers,
https://arxiv.org/abs/2604.17847, Conjecture 4.4, with Definition 1.1.
Credit: @pyaf

For a prime p, z(p) is the rank of apparition: the least k > 0 with p ∣ F_k. The Pisano period
π(q) is the least period of (F_m mod q). For an odd prime q, S(q) is the set of residues
r mod π(q) such that q ∣ φ(F_m) for every m ≡ r (mod π(q)); here a residue is its
representative in [0, π(q)).
-/

namespace OMA.S_arxiv_2604_17847

noncomputable def pisano (m : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ ∀ n : ℕ, Nat.fib (n + k) ≡ Nat.fib n [MOD m]}

noncomputable def rankOfApparition (p : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ p ∣ Nat.fib k}

def S (q : ℕ) : Set ℕ :=
  {r | r < pisano q ∧ ∀ m : ℕ, m ≡ r [MOD pisano q] → q ∣ Nat.totient (Nat.fib m)}

theorem main :
    ∀ q : ℕ, q.Prime → q ≠ 2 → (S q).Nonempty →
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q := by
  sorry

end OMA.S_arxiv_2604_17847
