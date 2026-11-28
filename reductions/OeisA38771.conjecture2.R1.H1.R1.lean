import OMAReductions.R_OeisA38771_conjecture2_R1

/-! Certify the finite A038771 semiprime range by supplying prime sums with small composite
offsets. Each offset bounds the least admissible composite from above. Its least prime factor
cannot occur in the primorial, and a composite below the cube of that factor is semiprime.
The ranges divide the elliptic primality certificates into files below the project size limit.
The finite data were tabulated by Dmitry Kamenetsky. The least-factor observation also occurs
in the proof of the adjacent lower-bound step by ivillar. -/

namespace OMA.R_OeisA38771_conjecture2_R1_H1_R1

def H1 : Prop := ∀ n : ℕ, n ≤ 82 →
    ∃ c : ℕ, 1 < c ∧ ¬c.Prime ∧ ((∏ j ∈ Finset.range n, Nat.nth Nat.Prime j) + c).Prime ∧ c < (Nat.nth Nat.Prime n)^3

def H2 : Prop := ∀ n : ℕ, 83 ≤ n → n ≤ 105 →
    ∃ c : ℕ, 1 < c ∧ ¬c.Prime ∧ ((∏ j ∈ Finset.range n, Nat.nth Nat.Prime j) + c).Prime ∧ c < (Nat.nth Nat.Prime n)^3

def H3 : Prop := ∀ n : ℕ, 106 ≤ n → n ≤ 120 →
    ∃ c : ℕ, 1 < c ∧ ¬c.Prime ∧ ((∏ j ∈ Finset.range n, Nat.nth Nat.Prime j) + c).Prime ∧ c < (Nat.nth Nat.Prime n)^3

def H4 : Prop := ∀ n : ℕ, 121 ≤ n → n ≤ 133 →
    ∃ c : ℕ, 1 < c ∧ ¬c.Prime ∧ ((∏ j ∈ Finset.range n, Nat.nth Nat.Prime j) + c).Prime ∧ c < (Nat.nth Nat.Prime n)^3

theorem semiprime_below_cube {m p : ℕ} (hm : 1 < m) (composite : ¬m.Prime)
    (lower : p ≤ m.minFac) (upper : m < p ^ 3) : m.IsSemiprime := by
  have prime := Nat.minFac_prime (by omega : m ≠ 1)
  obtain ⟨d, eq⟩ := Nat.minFac_dvd m
  have positive : 0 < d := by
    by_contra! bad
    have zero : d = 0 := by omega
    rw [zero, Nat.mul_zero] at eq
    omega
  have nonunit : d ≠ 1 := by
    intro hd
    have same : m = m.minFac := by simpa only [hd, Nat.mul_one] using eq
    exact composite (same.symm ▸ prime)
  have dprime : d.Prime := by
    by_contra bad
    have dq := Nat.minFac_prime nonunit
    have divides : d ∣ m := ⟨m.minFac, eq.trans (Nat.mul_comm _ _)⟩
    have factor := Nat.minFac_le_of_dvd dq.two_le ((Nat.minFac_dvd d).trans divides)
    have square := Nat.minFac_sq_le_self positive bad
    have product : p * p^2 ≤ m.minFac * d :=
      Nat.mul_le_mul lower ((Nat.pow_le_pow_left (lower.trans factor) 2).trans square)
    have cubed : p^3 ≤ m := by
      calc
        p^3 = p * p^2 := by ring
        _ ≤ m.minFac * d := product
        _ = m := eq.symm
    exact (not_lt_of_ge cubed) upper
  exact eq.symm ▸ prime.mul_isAlmostPrime_two dprime

theorem of_upper_witness {n c : ℕ} (large : 1 < c) (composite : ¬c.Prime)
    (primeSum : ((∏ j ∈ Finset.range n, Nat.nth Nat.Prime j) + c).Prime)
    (small : c < (Nat.nth Nat.Prime n)^3) : (OeisA38771.a n).IsSemiprime := by
  let S : Set ℕ := {b | (1 < b ∧ ¬b.Prime) ∧ ((∏ j ∈ Finset.range n, Nat.nth Nat.Prime j) + b).Prime}
  have member : c∈S := ⟨⟨large,composite⟩,primeSum⟩
  have least := Nat.sInf_mem (show S.Nonempty from ⟨c,member⟩)
  change (1 < sInf S ∧ ¬(sInf S).Prime) ∧ ((∏ j ∈ Finset.range n, Nat.nth Nat.Prime j) + sInf S).Prime at least
  change (sInf S).IsSemiprime
  have cap : sInf S < (Nat.nth Nat.Prime n)^3 := lt_of_le_of_lt (Nat.sInf_le member) small
  apply semiprime_below_cube least.1.1 least.1.2 _ cap
  have size := least.1.1
  have fac := Nat.minFac_prime (by omega : sInf S ≠ 1)
  by_contra! early
  have count := (Nat.count_le_iff_le_nth (p := Nat.Prime) Nat.infinite_setOfPred_prime).mpr early
  rw [Nat.count_succ, if_pos fac] at count
  have divprod : (sInf S).minFac ∣ (∏ j ∈ Finset.range n, Nat.nth Nat.Prime j) := by
    conv_lhs => rw [← Nat.nth_count fac]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (by omega))
  have divisor := dvd_add divprod (Nat.minFac_dvd (sInf S))
  have equal := (Nat.prime_dvd_prime_iff_eq fac least.2).mp divisor
  have le := Nat.minFac_le (show 0 < sInf S by omega)
  have pos : 0 < (∏ j ∈ Finset.range n, Nat.nth Nat.Prime j) :=
    Finset.prod_pos fun i _ => (Nat.prime_nth_prime i).pos
  omega

theorem main : H1 → H2 → H3 → H4 → OMA.R_OeisA38771_conjecture2_R1.H1 := by
  intro h₁ h₂ h₃ h₄ n hn
  have candidates : ∃ c : ℕ, 1 < c ∧ ¬c.Prime ∧ ((∏ j ∈ Finset.range n, Nat.nth Nat.Prime j) + c).Prime ∧ c < (Nat.nth Nat.Prime n)^3 := by
    by_cases small : n ≤ 82
    · exact h₁ n small
    by_cases mid : n ≤ 105
    · exact h₂ n (by omega) mid
    by_cases large : n ≤ 120
    · exact h₃ n (by omega) large
    exact h₄ n (by omega) hn
  obtain ⟨c, size, composite, primeSum, upper⟩ := candidates
  exact of_upper_witness size composite primeSum upper

end OMA.R_OeisA38771_conjecture2_R1_H1_R1
