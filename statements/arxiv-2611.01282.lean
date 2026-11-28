import Mathlib

/-!
# Small-LCM distinct covering systems via segmented local search

Source: https://arxiv.org/abs/2611.01282 (Jiheng Zhang), abstract, Definition 1 and Theorem 1.
Credit: @ivillar

Abstract of the source: We construct distinct covering systems with minimum moduli $8, 9, 10, 11$
and least common multiples $20160, 75600, 302400, 3326400$, respectively.

Formalization notes:
* Definition 1 of the source: a covering system is a finite collection of residue classes
  $a_i \pmod{m_i}$, $1 \le i \le n$, with $m_i \ge 2$ and $0 \le a_i < m_i$, whose union is
  $\mathbb{Z}$. The system is distinct if its moduli are pairwise distinct; its minimum modulus
  is the least $m_i$, and $L = \mathrm{lcm}(m_1, \ldots, m_n)$.
* A system is recorded as the finite set of the pairs $(a_i, m_i)$.
* `main` is the result that the abstract announces as constructed (Theorem 1 of the source):
  the existence of the four systems. The abstract also conjectures that these four least common
  multiples are minimal (Conjecture 1 of the source); that conjecture is not asserted here.
-/

namespace OMA.S_arxiv_2611_01282

/-- A distinct covering system, as a finite set of pairs `(a, m)` standing for the residue classes
`a (mod m)`: `m ≥ 2` and `a < m`, the moduli are pairwise distinct, and the classes cover `ℤ`. -/
def IsDistinctCoveringSystem (S : Finset (ℕ × ℕ)) : Prop :=
  (∀ c ∈ S, 2 ≤ c.2 ∧ c.1 < c.2) ∧
  (∀ c ∈ S, ∀ c' ∈ S, c.2 = c'.2 → c = c') ∧
  ∀ x : ℤ, ∃ c ∈ S, x ≡ (c.1 : ℤ) [ZMOD (c.2 : ℤ)]

/-- The system `S` has minimum modulus `m` and the least common multiple of its moduli is `L`. -/
def HasMinModulusAndLcm (S : Finset (ℕ × ℕ)) (m L : ℕ) : Prop :=
  IsLeast (Prod.snd '' (S : Set (ℕ × ℕ))) m ∧ S.lcm Prod.snd = L

theorem main :
    (∃ S, IsDistinctCoveringSystem S ∧ HasMinModulusAndLcm S 8 20160) ∧
    (∃ S, IsDistinctCoveringSystem S ∧ HasMinModulusAndLcm S 9 75600) ∧
    (∃ S, IsDistinctCoveringSystem S ∧ HasMinModulusAndLcm S 10 302400) ∧
    (∃ S, IsDistinctCoveringSystem S ∧ HasMinModulusAndLcm S 11 3326400) := by
  sorry

end OMA.S_arxiv_2611_01282
