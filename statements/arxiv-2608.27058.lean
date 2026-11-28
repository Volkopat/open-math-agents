import Mathlib

/-!
# Preperiods of the Euler zigzag numbers modulo odd prime powers

Berke Güleç, Modular periodicity of the Euler up/down numbers at odd prime powers,
https://arxiv.org/abs/2608.27058, Conjecture 6.5, with the definitions of Section 2.
Credit: @pyaf

E_n is the number of alternating (up/down) permutations σ of {0, …, n-1}, those with
σ(0) < σ(1) > σ(2) < ⋯. The sequence (E_n mod q) is eventually periodic, and its preperiod
s(q) is the least t such that E_{n+P} ≡ E_n (mod q) for some P ≥ 1 and all n ≥ t
(by Lemma 2.2 of the paper this is the minimal threshold for the minimal period).
-/

namespace OMA.S_arxiv_2608_27058

def zigzag (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ∀ i j : Fin n, j.val = i.val + 1 → (σ i < σ j ↔ Even i.val)).card

noncomputable def preperiod (q : ℕ) : ℕ :=
  sInf {t : ℕ | ∃ P, 0 < P ∧ ∀ n, t ≤ n → zigzag (n + P) ≡ zigzag n [MOD q]}

theorem main : ∀ p r : ℕ, p.Prime → p ≠ 2 → 2 ≤ r → r - 2 ≤ preperiod (p ^ r) := by
  sorry

end OMA.S_arxiv_2608_27058
