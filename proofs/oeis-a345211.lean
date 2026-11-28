import OMAStatements.S_oeis_a345211

namespace OMA.S_oeis_a345211






instance : DecidablePred InA345211 := fun n =>
  inferInstanceAs (Decidable (0 < n ∧ (oddRef n).card = (evenRef n).card))


instance : DecidablePred InA157932 := fun k =>
  inferInstanceAs (Decidable (((3 ^ (35 * k) + 5 ^ (21 * k) + 7 ^ (15 * k)) % 105).Prime))

theorem tau_two_mul {d : ℕ} (hd : Odd d) :
    (Nat.divisors (2 * d)).card = 2 * (Nat.divisors d).card := by
  rw [Nat.Coprime.card_divisors_mul (Nat.coprime_two_left.mpr hd)]
  rfl

theorem tau_four_mul {d : ℕ} (hd : Odd d) :
    (Nat.divisors (4 * d)).card = 3 * (Nat.divisors d).card := by
  have h : Nat.Coprime 4 d := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hd)
    simpa using this
  rw [Nat.Coprime.card_divisors_mul h]
  rfl

theorem refac_two_mul {d : ℕ} (hd : Odd d) : Refac (2 * d) ↔ Refac d := by
  unfold Refac
  rw [tau_two_mul hd]
  exact Nat.mul_dvd_mul_iff_left (by norm_num)

theorem refac_four_mul {d : ℕ} (hd : Odd d) (h : Refac (4 * d)) : 3 ∣ d := by
  unfold Refac at h
  rw [tau_four_mul hd] at h
  have h3 : 3 ∣ 4 * d := Dvd.dvd.trans (Dvd.intro _ rfl) h
  exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 4) h3

theorem exists_four (n : ℕ) (hn : 0 < n) :
    (∃ x ∈ Nat.divisors n, 4 ∣ x ∧ Refac x) ↔ (8 ∣ n ∨ 12 ∣ n) := by
  constructor
  · rintro ⟨x, hx, h4, hr⟩
    have hxn : x ∣ n := (Nat.mem_divisors.mp hx).1
    by_cases h8 : 8 ∣ x
    · exact Or.inl (h8.trans hxn)
    · obtain ⟨o, rfl⟩ := h4
      have ho : Odd o := by
        rw [Nat.odd_iff]
        omega
      have h3 := refac_four_mul ho hr
      right
      exact (show 12 ∣ 4 * o by omega).trans hxn
  · rintro (h | h)
    · exact ⟨8, Nat.mem_divisors.mpr ⟨h, by omega⟩, by norm_num, by decide⟩
    · exact ⟨12, Nat.mem_divisors.mpr ⟨h, by omega⟩, by norm_num, by decide⟩

theorem card_even (n : ℕ) (hn : 0 < n) (he : 2 ∣ n) :
    (evenRef n).card =
      (oddRef n).card + ((Nat.divisors n).filter (fun x => 4 ∣ x ∧ Refac x)).card := by
  rw [← Finset.card_filter_add_card_filter_not (fun x => 4 ∣ x) (s := evenRef n)]
  have h1 : (evenRef n).filter (fun x => 4 ∣ x) =
      (Nat.divisors n).filter (fun x => 4 ∣ x ∧ Refac x) := by
    ext x
    simp only [evenRef, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx, -, hr⟩, h4⟩
      exact ⟨hx, h4, hr⟩
    · rintro ⟨hx, h4, hr⟩
      exact ⟨⟨hx, even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans h4), hr⟩, h4⟩
  have h2 : ((evenRef n).filter (fun x => ¬ 4 ∣ x)).card = (oddRef n).card := by
    apply Finset.card_nbij' (fun x => x / 2) (fun d => 2 * d)
    · intro x hx
      simp only [Finset.mem_coe, evenRef, oddRef, Finset.mem_filter, Nat.mem_divisors] at hx ⊢
      obtain ⟨⟨⟨hxn, hn0⟩, hev, hr⟩, h4⟩ := hx
      have hx2 : x % 2 = 0 := Nat.even_iff.mp hev
      have hodd : Odd (x / 2) := by
        rw [Nat.odd_iff]
        omega
      have hxe : x = 2 * (x / 2) := by omega
      refine ⟨⟨(Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hx2)).trans hxn, hn0⟩, hodd, ?_⟩
      rw [← refac_two_mul hodd, ← hxe]
      exact hr
    · intro d hd
      simp only [Finset.mem_coe, evenRef, oddRef, Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      obtain ⟨⟨hdn, hn0⟩, hodd, hr⟩ := hd
      have hd2 : d % 2 = 1 := Nat.odd_iff.mp hodd
      refine ⟨⟨⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.mpr hodd) he hdn, hn0⟩,
        even_two_mul d, (refac_two_mul hodd).mpr hr⟩, ?_⟩
      omega
    · intro x hx
      simp only [Finset.mem_coe, evenRef, Finset.mem_filter] at hx
      have hx2 : x % 2 = 0 := Nat.even_iff.mp hx.1.2.1
      show 2 * (x / 2) = x
      omega
    · intro d hd
      show 2 * d / 2 = d
      omega
  rw [h1, h2, add_comm]

/-- The terms of A345211 are the n = 2m with neither 4 nor 6 dividing m. -/
theorem charact (n : ℕ) : InA345211 n ↔ 0 < n ∧ 2 ∣ n ∧ ¬ 8 ∣ n ∧ ¬ 12 ∣ n := by
  unfold InA345211
  constructor
  · rintro ⟨hn, hc⟩
    by_cases he : 2 ∣ n
    · have hs := card_even n hn he
      have hR : ((Nat.divisors n).filter (fun x => 4 ∣ x ∧ Refac x)).card = 0 := by omega
      have hnone : ¬ ∃ x ∈ Nat.divisors n, 4 ∣ x ∧ Refac x := by
        rintro ⟨x, hx, h4, hr⟩
        rw [Finset.card_eq_zero] at hR
        have hmem : x ∈ (Nat.divisors n).filter (fun x => 4 ∣ x ∧ Refac x) :=
          Finset.mem_filter.mpr ⟨hx, h4, hr⟩
        rw [hR] at hmem
        exact absurd hmem (Finset.notMem_empty x)
      rw [exists_four n hn] at hnone
      exact ⟨hn, he, fun h => hnone (Or.inl h), fun h => hnone (Or.inr h)⟩
    · exfalso
      have h1 : 1 ∈ oddRef n := by
        simp only [oddRef, Finset.mem_filter, Nat.mem_divisors]
        exact ⟨⟨one_dvd n, by omega⟩, odd_one, by decide⟩
      have h0 : evenRef n = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        simp only [evenRef, Finset.mem_filter, Nat.mem_divisors] at hx
        exact he ((even_iff_two_dvd.mp hx.2.1).trans hx.1.1)
      have hpos : 0 < (oddRef n).card := Finset.card_pos.mpr ⟨1, h1⟩
      rw [hc, h0, Finset.card_empty] at hpos
      exact absurd hpos (lt_irrefl 0)
  · rintro ⟨hn, he, h8, h12⟩
    refine ⟨hn, ?_⟩
    have hs := card_even n hn he
    have hR : (Nat.divisors n).filter (fun x => 4 ∣ x ∧ Refac x) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have h := (exists_four n hn).mp ⟨x, (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
      rcases h with h | h
      · exact h8 h
      · exact h12 h
    rw [hR, Finset.card_empty] at hs
    omega

/-- The residue of A157932's expression modulo 105. -/
def r (k : ℕ) : ℕ := (3 ^ (35 * k) + 5 ^ (21 * k) + 7 ^ (15 * k)) % 105

theorem m3 : 3 ^ 421 ≡ 3 ^ 1 [MOD 105] := by decide +kernel

theorem m5 : 5 ^ 253 ≡ 5 ^ 1 [MOD 105] := by decide +kernel

theorem m7 : 7 ^ 181 ≡ 7 ^ 1 [MOD 105] := by decide +kernel

theorem shift (b e c d : ℕ) (h : e = c + d) : b ^ e = b ^ c * b ^ d := by rw [h, pow_add]

theorem r_period (k : ℕ) : r (k + 13) = r (k + 1) := by
  have e3 : 3 ^ (35 * (k + 13)) ≡ 3 ^ (35 * (k + 1)) [MOD 105] := by
    rw [shift 3 (35 * (k + 13)) (35 * k + 34) 421 (by ring),
      shift 3 (35 * (k + 1)) (35 * k + 34) 1 (by ring)]
    exact Nat.ModEq.mul_left (3 ^ (35 * k + 34)) m3
  have e5 : 5 ^ (21 * (k + 13)) ≡ 5 ^ (21 * (k + 1)) [MOD 105] := by
    rw [shift 5 (21 * (k + 13)) (21 * k + 20) 253 (by ring),
      shift 5 (21 * (k + 1)) (21 * k + 20) 1 (by ring)]
    exact Nat.ModEq.mul_left (5 ^ (21 * k + 20)) m5
  have e7 : 7 ^ (15 * (k + 13)) ≡ 7 ^ (15 * (k + 1)) [MOD 105] := by
    rw [shift 7 (15 * (k + 13)) (15 * k + 14) 181 (by ring),
      shift 7 (15 * (k + 1)) (15 * k + 14) 1 (by ring)]
    exact Nat.ModEq.mul_left (7 ^ (15 * k + 14)) m7
  have e := (e3.add e5).add e7
  unfold Nat.ModEq at e
  unfold r
  exact e

theorem r_mod (k : ℕ) : r (k + 1) = r (k % 12 + 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h : k < 12
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 12 := ⟨k - 12, by omega⟩
      rw [show j + 12 + 1 = j + 13 by ring, r_period, ih j (by omega)]
      congr 2
      omega

theorem residues : ∀ t < 12, (r (t + 1)).Prime ↔ ((t + 1) % 12 = 0 ∨ (t + 1) % 12 = 4 ∨
    (t + 1) % 12 = 6 ∨ (t + 1) % 12 = 8) := by
  decide +kernel

theorem A157932_iff (k : ℕ) :
    InA157932 k ↔ (k % 12 = 0 ∨ k % 12 = 4 ∨ k % 12 = 6 ∨ k % 12 = 8) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [InA157932, Nat.zero_mod, true_or, iff_true]
    norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h := residues (j % 12) (Nat.mod_lt _ (by norm_num))
    have e : (j % 12 + 1) % 12 = (j + 1) % 12 := by omega
    rw [e] at h
    show (r (j + 1)).Prime ↔ _
    rw [r_mod]
    exact h

/-- The conjecture of A345211: every term is even, and for m >= 1, 2m is a term iff m is not in
A157932. -/
theorem conjecture :
    (∀ n, InA345211 n → Even n) ∧ (∀ m, 0 < m → (InA345211 (2 * m) ↔ ¬ InA157932 m)) := by
  refine ⟨fun n hn => even_iff_two_dvd.mpr ((charact n).mp hn).2.1, fun m hm => ?_⟩
  rw [charact, A157932_iff]
  omega

end OMA.S_oeis_a345211

theorem OMA.solution : type_of% @OMA.S_oeis_a345211.main :=
  OMA.S_oeis_a345211.conjecture
