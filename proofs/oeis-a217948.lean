import OMAStatements.S_oeis_a217948

/-! The riffle-orbit characterization, following @agchua (#22070).
Retain the modular iteration and forward argument. In the converse, use the
primitive-root power theorem on the quotient of the two nonzero residues. -/

open OMA.S_oeis_a217948 in
theorem OMA.solution : type_of% @OMA.S_oeis_a217948.main := by
  -- the riffle multiplies r - 1 by 2 modulo 2n - 1 and keeps the cards 2..2n-1
  have hstep : ∀ n r : ℕ, 2 ≤ n → 2 ≤ r → r ≤ 2 * n - 1 →
      2 ≤ riffle n r ∧ riffle n r ≤ 2 * n - 1 ∧
      ((riffle n r - 1 : ℕ) : ZMod (2 * n - 1)) = 2 * ((r - 1 : ℕ) : ZMod (2 * n - 1)) := by
    intro n r hn hr1 hr2
    unfold riffle
    split_ifs with h
    · refine ⟨by omega, by omega, ?_⟩
      rw [show 2 * r - 1 - 1 = 2 * (r - 1) by omega, Nat.cast_mul, Nat.cast_ofNat]
    · refine ⟨by omega, by omega, ?_⟩
      have hc : ((2 * n - 1 : ℕ) : ZMod (2 * n - 1)) = 0 := ZMod.natCast_self _
      rw [show 2 * r - 2 * n - 1 = 2 * (r - 1) - (2 * n - 1) by omega,
        Nat.cast_sub (by omega : 2 * n - 1 ≤ 2 * (r - 1)), hc, sub_zero, Nat.cast_mul,
        Nat.cast_ofNat]
  -- iterating: the k-th iterate multiplies r - 1 by 2^k
  have hiter : ∀ n r k : ℕ, 2 ≤ n → 2 ≤ r → r ≤ 2 * n - 1 →
      2 ≤ (riffle n)^[k] r ∧ (riffle n)^[k] r ≤ 2 * n - 1 ∧
      (((riffle n)^[k] r - 1 : ℕ) : ZMod (2 * n - 1)) =
        2 ^ k * ((r - 1 : ℕ) : ZMod (2 * n - 1)) := by
    intro n r k hn hr1 hr2
    induction k with
    | zero => exact ⟨hr1, hr2, by simp⟩
    | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨g1, g2, g3⟩ := hstep n ((riffle n)^[k] r) hn h1 h2
      rw [Function.iterate_succ_apply']
      refine ⟨g1, g2, ?_⟩
      rw [g3, h3]
      ring
  -- natural numbers below N with the same residue are equal
  have hcast : ∀ N x y : ℕ, x < N → y < N → (x : ZMod N) = (y : ZMod N) → x = y := by
    intro N x y hx hy h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
    exact h
  -- one orbit implies that 2n - 1 is a prime with primitive root 2
  have hfwd : ∀ n : ℕ, 2 ≤ n →
      (∀ r ∈ Finset.Icc 2 (2 * n - 1), ∀ s ∈ Finset.Icc 2 (2 * n - 1),
        ∃ k : ℕ, (riffle n)^[k] r = s) → IsA001122 (2 * n - 1) := by
    intro n hn horb
    have hNZ : NeZero (2 * n - 1) := ⟨by omega⟩
    have hpow : ∀ x : ℕ, 1 ≤ x → x ≤ 2 * n - 2 →
        ∃ k : ℕ, ((x : ℕ) : ZMod (2 * n - 1)) = 2 ^ k := by
      intro x hx1 hx2
      obtain ⟨k, hk⟩ := horb 2 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) (x + 1)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      obtain ⟨_, _, h3⟩ := hiter n 2 k hn le_rfl (by omega)
      refine ⟨k, ?_⟩
      rw [hk, show x + 1 - 1 = x by omega, show (2 - 1 : ℕ) = 1 from rfl, Nat.cast_one,
        mul_one] at h3
      exact h3
    have hcop2 : Nat.Coprime 2 (2 * n - 1) := by
      rw [Nat.coprime_two_left]
      exact ⟨n - 1, by omega⟩
    have hu2 : IsUnit (2 : ZMod (2 * n - 1)) := by
      have h := (ZMod.isUnit_iff_coprime 2 (2 * n - 1)).mpr hcop2
      rwa [Nat.cast_ofNat] at h
    have hprime : (2 * n - 1).Prime := by
      by_contra hnp
      obtain ⟨d, hd, hd2, hdlt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
      obtain ⟨k, hk⟩ := hpow d (by omega) (by omega)
      have hud : IsUnit ((d : ℕ) : ZMod (2 * n - 1)) := by
        rw [hk]
        exact hu2.pow k
      have hcd : Nat.Coprime d (2 * n - 1) := (ZMod.isUnit_iff_coprime d (2 * n - 1)).mp hud
      have hd1 := Nat.Coprime.eq_one_of_dvd hcd hd
      omega
    have hfact : Fact (2 * n - 1).Prime := ⟨hprime⟩
    unfold IsA001122
    refine ⟨hprime, ?_⟩
    have h2ne : (2 : ZMod (2 * n - 1)) ≠ 0 := hu2.ne_zero
    have hdvd : orderOf (2 : ZMod (2 * n - 1)) ∣ 2 * n - 1 - 1 :=
      orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h2ne)
    have hle : orderOf (2 : ZMod (2 * n - 1)) ≤ 2 * n - 1 - 1 := Nat.le_of_dvd (by omega) hdvd
    have hpos : 0 < orderOf (2 : ZMod (2 * n - 1)) := Nat.pos_of_dvd_of_pos hdvd (by omega)
    have hsub : Finset.univ.erase (0 : ZMod (2 * n - 1)) ⊆
        (Finset.range (orderOf (2 : ZMod (2 * n - 1)))).image
          (fun j : ℕ => (2 : ZMod (2 * n - 1)) ^ j) := by
      intro y hy
      rw [Finset.mem_erase] at hy
      have hv1 : 1 ≤ y.val := by
        by_contra h0
        have h0' : y.val = 0 := by omega
        rw [ZMod.val_eq_zero] at h0'
        exact hy.1 h0'
      have hv2 := ZMod.val_lt y
      obtain ⟨k, hk⟩ := hpow y.val hv1 (by omega)
      rw [Finset.mem_image]
      refine ⟨k % orderOf (2 : ZMod (2 * n - 1)), Finset.mem_range.mpr (Nat.mod_lt _ hpos), ?_⟩
      show (2 : ZMod (2 * n - 1)) ^ (k % orderOf (2 : ZMod (2 * n - 1))) = y
      rw [pow_mod_orderOf, ← hk, ZMod.natCast_zmod_val]
    have hcard := Finset.card_le_card hsub
    have hc1 : (Finset.univ.erase (0 : ZMod (2 * n - 1))).card = 2 * n - 1 - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    have hc2 := (Finset.card_image_le (s := Finset.range (orderOf (2 : ZMod (2 * n - 1))))
      (f := fun j : ℕ => (2 : ZMod (2 * n - 1)) ^ j))
    rw [Finset.card_range] at hc2
    omega
  -- conversely, a prime 2n - 1 with primitive root 2 gives one orbit
  have hbwd : ∀ n : ℕ, 2 ≤ n → IsA001122 (2 * n - 1) →
      ∀ r ∈ Finset.Icc 2 (2 * n - 1), ∀ s ∈ Finset.Icc 2 (2 * n - 1),
        ∃ k : ℕ, (riffle n)^[k] r = s := by
    intro n hn hA r hr s hs
    unfold IsA001122 at hA
    obtain ⟨hprime, hord⟩ := hA
    have hfact : Fact (2 * n - 1).Prime := ⟨hprime⟩
    have hNZ : NeZero (2 * n - 1) := ⟨by omega⟩
    rw [Finset.mem_Icc] at hr hs
    obtain ⟨hr1, hr2⟩ := hr
    obtain ⟨hs1, hs2⟩ := hs
    have hu : ((r - 1 : ℕ) : ZMod (2 * n - 1)) ≠ 0 := by
      intro h0
      have h2 : ((r - 1 : ℕ) : ZMod (2 * n - 1)) = ((0 : ℕ) : ZMod (2 * n - 1)) := by
        rw [Nat.cast_zero]
        exact h0
      have h20 := hcast _ (r - 1) 0 (by omega) (by omega) h2
      omega
    have hv : ((s - 1 : ℕ) : ZMod (2 * n - 1)) ≠ 0 := by
      intro h0
      have h2 : ((s - 1 : ℕ) : ZMod (2 * n - 1)) = ((0 : ℕ) : ZMod (2 * n - 1)) := by
        rw [Nat.cast_zero]
        exact h0
      have h20 := hcast _ (s - 1) 0 (by omega) (by omega) h2
      omega
    have : NeZero (2 * n - 1 - 1) := ⟨by omega⟩
    have hroot : IsPrimitiveRoot (2 : ZMod (2 * n - 1)) (2 * n - 1 - 1) := by
      rw [← hord]
      exact IsPrimitiveRoot.orderOf _
    obtain ⟨j, _, hj⟩ := hroot.eq_pow_of_pow_eq_one
      (ZMod.pow_card_sub_one_eq_one (div_ne_zero hv hu))
    have hj := (eq_div_iff hu).mp hj
    obtain ⟨g1, g2, g3⟩ := hiter n r j hn hr1 hr2
    refine ⟨j, ?_⟩
    have hj' : (((riffle n)^[j] r - 1 : ℕ) : ZMod (2 * n - 1)) =
        ((s - 1 : ℕ) : ZMod (2 * n - 1)) := by
      rw [g3]
      exact hj
    have hjs := hcast _ _ _ (by omega) (by omega) hj'
    omega
  -- the terms are exactly the numbers p + 1 with p in A001122
  have hchar : ∀ m : ℕ, IsTerm m ↔ ∃ p : ℕ, IsA001122 p ∧ m = p + 1 := by
    intro m
    constructor
    · intro hm
      unfold IsTerm at hm
      obtain ⟨n, hn, rfl, horb⟩ := hm
      exact ⟨2 * n - 1, hfwd n hn horb, by omega⟩
    · rintro ⟨p, hp, rfl⟩
      have hp' := hp
      unfold IsA001122 at hp'
      obtain ⟨hpp, hpo⟩ := hp'
      have hp2 : p ≠ 2 := by
        rintro rfl
        have h1 : (2 : ZMod 2) ^ orderOf (2 : ZMod 2) = 1 := pow_orderOf_eq_one _
        rw [hpo] at h1
        revert h1
        decide
      obtain ⟨t, ht⟩ : ∃ t, p = 2 * t + 1 := by
        rcases hpp.eq_two_or_odd with h | h
        · exact absurd h hp2
        · exact ⟨p / 2, by omega⟩
      have ht1 : 1 ≤ t := by
        have := hpp.two_le
        omega
      have hp3 : 2 * (t + 1) - 1 = p := by omega
      unfold IsTerm
      refine ⟨t + 1, by omega, by omega, ?_⟩
      exact hbwd (t + 1) (by omega) (by rw [hp3]; exact hp)
  refine ⟨?_, hchar⟩
  intro m hm
  obtain ⟨p, hp, rfl⟩ := (hchar m).mp hm
  unfold IsA001122 at hp
  rw [Nat.add_sub_cancel]
  exact hp.1
