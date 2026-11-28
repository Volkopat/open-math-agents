import FormalConjectures.ErdosProblems.«269»

-- Reduction Erdos269.erdos_269.variants.irrational.R1 of Erdős Problem 269 — irrational
-- Credit: @timlantin

/-!
# Reduction R1 of Erdős Problem 269, variant `irrational`

Written with Claude Code (AI-assisted).

The statement asks for irrationality of the series for every finite set `P` of primes with
at least two elements.  We split by the size of `P`.

* `H1` is the two-prime case.  It is known on paper: Steve Fan (erdosproblems.com forum
  thread 269, 26 June 2026) proved that the series is even transcendental when `|P| = 2`, via
  the factorisation `S = S1 * S2`, the identity `(p-1) S1 + (q-1) S2 = p + q - 1` and the
  transcendence of Hecke-Mahler series.  An elementary irrationality proof along the same
  factorisation is possible (Dirichlet approximation of `log q / log p`).
* `H2` is the case of at least three primes.  As far as we know this is open: Fan remarks
  that his argument does not generalise since the series no longer factors, and the note of
  W. Cook (same thread, 11 September 2026) describes an obstruction without proving
  irrationality.

The reduction itself is only the case split `|P| = 2` or `|P| ≥ 3`.
-/

namespace OMA.R_Erdos269_erdos_269_variants_irrational_R1

/-- Two primes: the series over the `{p, q}`-smooth numbers is irrational. -/
def H1 : Prop := ∀ p q : ℕ, p.Prime → q.Prime → p < q →
  Irrational (Erdos269.series ({p, q} : Set ℕ))

/-- At least three primes. -/
def H2 : Prop := ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → 3 ≤ P.card →
  Irrational (Erdos269.series (P : Set ℕ))

theorem main : H1 → H2 → type_of% @Erdos269.erdos_269.variants.irrational := by
  intro h1 h2 P hP hcard
  rcases Nat.lt_or_ge P.card 3 with h3 | h3
  · have h2c : P.card = 2 := by omega
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2c
    have hx : x.Prime := hP x (by simp)
    have hy : y.Prime := hP y (by simp)
    rcases Nat.lt_or_gt_of_ne hxy with hlt | hlt
    · have h := h1 x y hx hy hlt
      rwa [← Finset.coe_pair] at h
    · have h := h1 y x hy hx hlt
      rwa [← Finset.coe_pair, Finset.pair_comm] at h
  · exact h2 P hP h3

end OMA.R_Erdos269_erdos_269_variants_irrational_R1
