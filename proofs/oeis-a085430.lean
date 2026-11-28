import OMAStatements.S_oeis_a085430

/-! Following @schulzee (#26911), retain the general-linear-group cardinality
and least-dimension argument. Use finite-unit order facts directly for the
positivity and divisibility of the order of 2 modulo the odd prime. -/

namespace OMA.A085430

open Matrix

/-- An element of prime order `p` exists in `GL(m, 2)` exactly when `p` divides the order of
the group. -/
lemma exists_order_iff (p : ℕ) (hp : p.Prime) (m : ℕ) :
    (∃ g : GL (Fin m) (ZMod 2), orderOf g = p) ↔ p ∣ Nat.card (GL (Fin m) (ZMod 2)) := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨g, hg⟩
    rw [← hg]
    exact orderOf_dvd_natCard g
  · intro h
    rw [Nat.card_eq_fintype_card] at h
    exact exists_prime_orderOf_dvd_card p h

/-- An odd prime `p` divides the order of `GL(m, 2)` exactly when the order of 2 modulo `p` is
at most `m`. -/
lemma dvd_card_iff (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) :
    p ∣ Nat.card (GL (Fin m) (ZMod 2)) ↔ orderOf (2 : ZMod p) ≤ m := by
  have : Fact p.Prime := ⟨hp⟩
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hunit : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).mpr hcop.symm
  have hpow : ∀ d : ℕ, p ∣ 2 ^ d - 1 ↔ orderOf (2 : ZMod p) ∣ d := by
    intro d
    rw [orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff,
      Nat.cast_sub (Nat.one_le_two_pow), sub_eq_zero]
    push_cast
    rfl
  have hopos : 0 < orderOf (2 : ZMod p) := hunit.isOfFinOrder.orderOf_pos
  rw [Matrix.card_GL_field, ZMod.card, Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hp)]
  constructor
  · rintro ⟨i, -, hi⟩
    have hle : (i : ℕ) ≤ m := i.isLt.le
    have hfac : 2 ^ m - 2 ^ (i : ℕ) = 2 ^ (i : ℕ) * (2 ^ (m - (i : ℕ)) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hle]
    rw [hfac] at hi
    have hd : p ∣ 2 ^ (m - (i : ℕ)) - 1 := (hcop.pow_right _).dvd_of_dvd_mul_left hi
    have hdiv := (hpow _).mp hd
    have hpos : 0 < m - (i : ℕ) := Nat.sub_pos_of_lt i.isLt
    exact le_trans (Nat.le_of_dvd hpos hdiv) (Nat.sub_le _ _)
  · intro h
    have hlt : m - orderOf (2 : ZMod p) < m := by omega
    refine ⟨⟨m - orderOf (2 : ZMod p), hlt⟩, Finset.mem_univ _, ?_⟩
    have hfac : 2 ^ m - 2 ^ (m - orderOf (2 : ZMod p))
        = 2 ^ (m - orderOf (2 : ZMod p)) * (2 ^ orderOf (2 : ZMod p) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.sub_add_cancel h]
    show p ∣ 2 ^ m - 2 ^ (m - orderOf (2 : ZMod p))
    rw [hfac]
    exact Dvd.dvd.mul_left ((hpow _).mpr dvd_rfl) _

theorem result (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ)
    (hm : IsLeast {k : ℕ | ∃ g : GL (Fin k) (ZMod 2), orderOf g = p} m) : m ∣ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hset : ∀ k : ℕ, k ∈ {k : ℕ | ∃ g : GL (Fin k) (ZMod 2), orderOf g = p}
      ↔ orderOf (2 : ZMod p) ≤ k := by
    intro k
    rw [Set.mem_ofPred_eq, exists_order_iff p hp k, dvd_card_iff p hp hp2 k]
  have h1 : orderOf (2 : ZMod p) ≤ m := (hset m).mp hm.1
  have h2 : m ≤ orderOf (2 : ZMod p) := hm.2 ((hset _).mpr le_rfl)
  have hmo : m = orderOf (2 : ZMod p) := le_antisymm h2 h1
  rw [hmo]
  have hunit : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).mpr ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
  exact ZMod.orderOf_dvd_card_sub_one hunit.ne_zero

end OMA.A085430

theorem OMA.solution : type_of% @OMA.S_oeis_a085430.main :=
  fun p hp hp2 m hm => OMA.A085430.result p hp hp2 m hm
