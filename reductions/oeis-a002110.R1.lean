import OMAStatements.S_oeis_a002110

namespace OMA.R_oeis_a002110_R1

open OMA.S_oeis_a002110

lemma primorial_le_gap {n p q : ℕ} (h : GoodPair n p q) :
    primorialFirst n ≤ q - p := by
  classical
  obtain ⟨_, _, hpq, _, hcard⟩ := h
  let g := (p + 1).gcd (q + 1)
  have hc : g.primeFactors.card = n := by
    simpa [g, Nat.primeFactors_gcd (by omega : p + 1 ≠ 0) (by omega : q + 1 ≠ 0)] using hcard
  let e := g.primeFactors.orderEmbOfFin hc
  have he (i : Fin n) : (e i).Prime :=
    Nat.prime_of_mem_primeFactors (g.primeFactors.orderEmbOfFin_mem hc i)
  have hrank : ∀ i (hi : i < n), i ≤ Nat.count Nat.Prime (e ⟨i, hi⟩) := by
    intro i
    induction i with
    | zero => intro hi; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      have hi' : i < n := by omega
      exact (ih hi').trans_lt (Nat.count_strict_mono (he ⟨i, hi'⟩)
        (e.strictMono (show (⟨i, hi'⟩ : Fin n) < ⟨i + 1, hi⟩ from Nat.lt_succ_self i)))
  have hle (i : Fin n) : Nat.nth Nat.Prime i ≤ e i := by
    calc
      Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime (e i)) :=
        (Nat.nth_monotone Nat.infinite_setOfPred_prime) (hrank i i.isLt)
      _ = e i := Nat.nth_count (he i)
  have hprod : primorialFirst n ≤ ∏ v ∈ g.primeFactors, v := by
    calc
      primorialFirst n = ∏ i : Fin n, Nat.nth Nat.Prime i := by
        simp only [primorialFirst, Fin.prod_univ_eq_prod_range]
      _ ≤ ∏ i : Fin n, e i := Finset.prod_le_prod' (fun i _ => hle i)
      _ = ∏ v ∈ g.primeFactors, v := by
        rw [← g.primeFactors.map_orderEmbOfFin_univ hc, Finset.prod_map]
        rfl
  have hd : g ∣ q - p := by
    simpa using Nat.dvd_sub (Nat.gcd_dvd_right (p + 1) (q + 1))
      (Nat.gcd_dvd_left (p + 1) (q + 1))
  exact hprod.trans (Nat.le_of_dvd (by omega) ((Nat.prod_primeFactors_dvd g).trans hd))
/-- For each size of the common prime factor set at least one suitable consecutive pair exists. -/
def H1 : Prop := ∀ n : ℕ, ∃ p q : ℕ, GoodPair n p q

/-- A pair whose gap exceeds the primorial is preceded by a pair with the same count. -/
def H2 : Prop := ∀ n p q : ℕ, GoodPair n p q → primorialFirst n < q - p →
    ∃ r s : ℕ, GoodPair n r s ∧ r < p

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a002110.main := by
  classical
  intro hex descent n
  let p := Nat.find (hex n)
  obtain ⟨q, hpq⟩ : ∃ q, GoodPair n p q := Nat.find_spec (hex n)
  have hmin : ∀ r s, GoodPair n r s → p ≤ r :=
    fun r s hrs => Nat.find_min' (hex n) ⟨s, hrs⟩
  refine ⟨p, q, hpq, hmin, le_antisymm ?_ (primorial_le_gap hpq)⟩
  apply Nat.le_of_not_gt
  intro hbig
  obtain ⟨r, s, hrs, hr⟩ := descent n p q hpq hbig
  exact (Nat.not_lt_of_ge (hmin r s hrs)) hr

end OMA.R_oeis_a002110_R1
