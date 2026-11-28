import Mathlib

/-!
# OEIS A285052

For each product `a * b` modulo `n`, replace the two factors and the
product by their respective idempotent powers. Count distinct ordered
triples of the resulting residues.

Source: https://oeis.org/A285052 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a285052

/-- An idempotent reached by a positive power of the residue `x`. -/
def idempotentPower {n : ℕ} (x e : ZMod n) : Prop :=
  IsIdempotentElem e ∧ ∃ k : ℕ, 0 < k ∧ x ^ k = e

/-- The triples obtained from the multiplication table of the residue ring. -/
def triples (n : ℕ) : Set (ZMod n × ZMod n × ZMod n) :=
  {t | ∃ a b : ZMod n, idempotentPower a t.1 ∧ idempotentPower b t.2.1 ∧
    idempotentPower (a * b) t.2.2}

theorem main :
    ∀ n : ℕ, 1 ≤ n → Nat.card (triples n) = 4 ^ n.primeFactors.card := by
  sorry

end OMA.S_oeis_a285052
