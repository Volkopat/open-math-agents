import OMAStatements.S_oeis_a307767

namespace OMA.S_oeis_a307767

lemma prime_case (n p x a t : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n)
    (hk : (n - 1) / 2 = 2 ^ a * t) (hx : x ^ 2 ≡ 2 [MOD n])
    (h2 : (2 : ZMod n) ^ ((n - 1) / 2) = -1) :
    2 ^ (a + 2) ∣ p - 1 := by
  haveI := Fact.mk hp
  have h2lt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  haveI : Fact (2 < p) := ⟨h2lt⟩
  have hy : ((x : ZMod p)) ^ 2 = 2 := by
    have h : ((x ^ 2 : ℕ) : ZMod p) = ((2 : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact hx.of_dvd hpn
    push_cast at h
    exact h
  have h2p : (2 : ZMod p) ^ ((n - 1) / 2) = -1 := by
    have := congrArg (ZMod.castHom hpn (ZMod p)) h2
    rw [map_pow, map_neg, map_one, map_ofNat] at this
    exact this
  obtain ⟨z, hz⟩ : ∃ z : ZMod p, z = (x : ZMod p) ^ t := ⟨_, rfl⟩
  have hz1 : z ^ (2 ^ (a + 1)) = -1 := by
    have e : t * 2 ^ (a + 1) = 2 * (2 ^ a * t) := by ring
    rw [hz, ← pow_mul, e, pow_mul, hy, ← hk, h2p]
  have hne : (-1 : ZMod p) ≠ 1 := ZMod.neg_one_ne_one
  have hz2 : z ^ (2 ^ (a + 1 + 1)) = 1 := by
    rw [pow_succ 2 (a + 1), pow_mul, hz1, neg_one_sq]
  have hord : orderOf z = 2 ^ (a + 1 + 1) :=
    orderOf_eq_prime_pow (by rw [hz1]; exact hne) hz2
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by positivity)] at hz1
    exact (neg_ne_zero.mpr one_ne_zero) hz1.symm
  have := ZMod.orderOf_dvd_card_sub_one hz0
  rw [hord] at this
  exact this

lemma two_nonres (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n)
    (h2 : (2 : ZMod n) ^ ((n - 1) / 2) = -1) (x : ℕ) (hx : x ^ 2 ≡ 2 [MOD n]) : False := by
  have hk0 : (n - 1) / 2 ≠ 0 := by omega
  obtain ⟨a, t, ht, hk⟩ := Nat.exists_eq_two_pow_mul_odd hk0
  have hnk : n - 1 = 2 * ((n - 1) / 2) := by
    obtain ⟨r, hr⟩ := hodd
    omega
  have key : ∀ m, m ∣ n → m ≡ 1 [MOD 2 ^ (a + 2)] := by
    intro m
    induction m using Nat.recOnMul
    next =>
      intro h
      rw [zero_dvd_iff] at h
      omega
    next =>
      intro _
      rfl
    next p hp =>
      intro hpn
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpn)
      have := prime_case n p x a t hp hp2 hpn hk hx h2
      exact ((Nat.modEq_iff_dvd' hp.one_le).mpr this).symm
    next u v iha ihb =>
      intro huv
      have := Nat.ModEq.mul (iha (dvd_trans (dvd_mul_right u v) huv))
        (ihb (dvd_trans (dvd_mul_left v u) huv))
      rwa [one_mul] at this
  have hn1 := key n dvd_rfl
  have hd : 2 ^ (a + 2) ∣ n - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hn1.symm
  rw [hnk, hk] at hd
  have h3 : 2 * 2 ^ a * 2 ∣ 2 * 2 ^ a * t := by
    rw [show 2 * 2 ^ a * 2 = 2 ^ (a + 2) by ring, show 2 * 2 ^ a * t = 2 * (2 ^ a * t) by ring]
    exact hd
  have h2t : 2 ∣ t := (mul_dvd_mul_iff_left (by positivity : (2 * 2 ^ a) ≠ 0)).mp h3
  exact (Nat.not_even_iff_odd.mpr ht) (even_iff_two_dvd.mpr h2t)

lemma A020649_eq (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n)
    (h2 : (2 : ZMod n) ^ ((n - 1) / 2) = -1) : A020649 n = 2 := by
  have hmem : 2 ∈ {q : ℕ | ¬ ∃ x : ℕ, x < n ∧ x ^ 2 ≡ q [MOD n]} := by
    rintro ⟨x, -, hx⟩
    exact two_nonres n hn hodd h2 x hx
  unfold A020649
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · apply le_csInf ⟨2, hmem⟩
    intro q hq
    by_contra hlt
    push_neg at hlt
    apply hq
    interval_cases q
    · exact ⟨0, by omega, by norm_num [Nat.ModEq]⟩
    · exact ⟨1, by omega, by norm_num [Nat.ModEq]⟩

end OMA.S_oeis_a307767

theorem OMA.solution : type_of% @OMA.S_oeis_a307767.main := by
  intro n hn hodd h2
  have hA := OMA.S_oeis_a307767.A020649_eq n hn hodd h2
  refine ⟨hA, fun hnp => ?_⟩
  unfold OMA.S_oeis_a307767.InA307767
  refine ⟨hodd, by omega, hnp, ?_⟩
  rw [hA]
  exact_mod_cast h2
