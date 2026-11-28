import OMAReductions.R_mse_3534503_R1

/-!
A prime dividing p² + p + 1 kills each block of three in the geometric
sum. The corresponding residue has order three unless it equals one.
-/

open scoped ArithmeticFunction.sigma

private theorem sumBlocksOfThree {R : Type} [CommRing R] (z : R)
    (hz : z ^ 2 + z + 1 = 0) (n : ℕ) :
    (∑ i ∈ Finset.range (3 * n), z ^ i) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 3 * (n + 1) = ((3 * n + 1) + 1) + 1 by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih, zero_add]
    calc
      _ = z ^ (3 * n) * (z ^ 2 + z + 1) := by
        rw [show (3 * n + 1) + 1 = 3 * n + 2 by omega]
        simp only [pow_add, pow_one]
        ring
      _ = 0 := by rw [hz, mul_zero]

theorem OMA.solution : OMA.R_mse_3534503_R1.H1 := by
  intro p t j m hp hc hd
  obtain ⟨q, hq, hqp⟩ := Nat.exists_prime_and_dvd (n := p ^ 2 + p + 1) (by
    have := hp.two_le
    omega)
  let _ : Fact q.Prime := ⟨hq⟩
  let z : ZMod q := p
  have hz : z ^ 2 + z + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff (p ^ 2 + p + 1) q).2 hqp
    push_cast at h
    exact h
  have hnonzero : z ≠ 0 := by
    intro h
    simp [h] at hz
  let k := (3 * j + 1) * 2
  have hcount : k + 1 = 3 * (2 * j + 1) := by dsimp [k]; omega
  have hSigma : q ∣ σ 1 (p ^ k) := by
    apply (ZMod.natCast_eq_zero_iff _ _).1
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, hcount]
    push_cast
    exact sumBlocksOfThree z hz _
  have hcop : Nat.Coprime (p ^ k) (t ^ 2) := (hc.pow_left k).pow_right 2
  have hfactor : (p ^ (3 * j + 1) * t) ^ 2 = p ^ k * t ^ 2 := by
    rw [mul_pow, ← pow_mul]
  have hSigFull : q ∣ σ 1 ((p ^ (3 * j + 1) * t) ^ 2) := by
    rw [hfactor, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
    exact dvd_mul_of_dvd_left hSigma _
  have hbase := hq.dvd_of_dvd_pow (hSigFull.trans hd)
  have hdprod := hq.dvd_of_dvd_pow hbase
  have hpNot : ¬ q ∣ p := fun h => hnonzero ((ZMod.natCast_eq_zero_iff p q).2 h)
  have hqt : q ∣ t := (hq.dvd_mul.mp hdprod).resolve_left (fun h =>
    hpNot (hq.dvd_of_dvd_pow h))
  refine ⟨q, hq, hqt, hqp, ?_⟩
  by_cases hzOne : z = 1
  · left
    have hThree : (3 : ZMod q) = 0 := calc
      (3 : ZMod q) = z ^ 2 + z + 1 := by rw [hzOne]; ring
      _ = 0 := hz
    have hdThree : q ∣ 3 := (ZMod.natCast_eq_zero_iff 3 q).1 hThree
    exact (Nat.dvd_prime_two_le (by decide : Nat.Prime 3) hq.two_le).1 hdThree
  · right
    have hCube : z ^ 3 = 1 := by
      linear_combination (z - 1) * hz
    let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hOrd : orderOf z = 3 := orderOf_eq_prime hCube hzOne
    have hOrderDvd := orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hnonzero)
    rw [hOrd] at hOrderDvd
    obtain ⟨b, hb⟩ := hOrderDvd
    have := hq.two_le
    omega

