import OMAStatements.S_oeis_a179194
open OMA.S_oeis_a179194

namespace OMA.P_a179194
open OMA.S_oeis_a179194

lemma digit_eq {b m k : ℕ} (hm : 0 < m) (hb : 0 < b) :
    digit b m k = b * (b ^ k % m) / m := by
  unfold digit
  have h1 : b ^ (k + 1) = m * (b * (b ^ k / m)) + b * (b ^ k % m) := by
    rw [pow_succ]
    conv_lhs => rw [← Nat.div_add_mod (b ^ k) m]
    ring
  have hlt : b * (b ^ k % m) / m < b := by
    rw [Nat.div_lt_iff_lt_mul hm]
    exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hm) hb
  rw [h1, Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.add_comm, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hlt

lemma period_of_modeq {b m p K : ℕ} (hm : 0 < m) (hb : 0 < b) (hp : 0 < p)
    (h : b ^ (K + p) ≡ b ^ K [MOD m]) : IsPeriod b m p := by
  refine ⟨hp, K, fun k hk => ?_⟩
  rw [digit_eq hm hb, digit_eq hm hb]
  have : b ^ (k + p) ≡ b ^ k [MOD m] := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    have := Nat.ModEq.mul_left (b ^ j) h
    rw [← pow_add, ← pow_add] at this
    rw [show K + j + p = j + (K + p) by ring, show K + j = j + K by ring]
    exact this
  rw [this]

/-- Remainders are determined by digits when `m < b`. -/
lemma rem_inj {b m r r' : ℕ} (hm : 0 < m) (hbm : m < b) (h : b * r / m = b * r' / m) : r = r' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : b * r / m + 1 ≤ b * r' / m := by
      rw [Nat.le_div_iff_mul_le hm, Nat.add_mul, one_mul]
      have := Nat.div_mul_le_self (b * r) m
      nlinarith
    omega
  · have : b * r' / m + 1 ≤ b * r / m := by
      rw [Nat.le_div_iff_mul_le hm, Nat.add_mul, one_mul]
      have := Nat.div_mul_le_self (b * r') m
      nlinarith
    omega

lemma cast_b (m : ℕ) : (((m + 2 : ℕ)) : ZMod m) = 2 := by
  push_cast; rw [ZMod.natCast_self, zero_add]

lemma inSeq_iff (q : ℕ) : InSeq (q + 2) ↔ PrimRoot2 q := by
  have hn2 : q + 2 - 2 = q := by omega
  have hn3 : q + 2 - 3 = q - 1 := by omega
  unfold InSeq
  rw [hn2, hn3]
  constructor
  · rintro ⟨-, hnt, hmem, hlb⟩
    have hq2 : 2 ≤ q := by have := hmem.1; omega
    have hq0 : q ≠ 0 := by omega
    obtain ⟨e, m', hodd, hqe⟩ := Nat.exists_eq_two_pow_mul_odd hq0
    have hm'pos : 0 < m' := hodd.pos
    have : NeZero m' := ⟨by omega⟩
    have hcop : Nat.Coprime (q + 2) m' := by
      have : q + 2 = 2 + (2 ^ e) * m' := by rw [hqe]; ring
      rw [this, Nat.coprime_add_mul_right_left]
      exact Nat.coprime_two_left.mpr hodd
    set p := orderOf ((q + 2 : ℕ) : ZMod m') with hpdef
    have htot : ((q + 2 : ℕ) : ZMod m') ^ (Nat.totient m') = 1 := by
      have := Nat.ModEq.pow_totient hcop
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr this
      push_cast at this ⊢; exact this
    have htotpos : 0 < Nat.totient m' := Nat.totient_pos.mpr hm'pos
    have hppos : 0 < p := orderOf_pos_iff.mpr
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, htotpos, htot⟩)
    have hple : p ≤ Nat.totient m' := Nat.le_of_dvd htotpos (orderOf_dvd_of_pow_eq_one htot)
    have hper : IsPeriod (q + 2) q p := by
      apply period_of_modeq (K := e) (by omega) (by omega) hppos
      have hd1 : m' ∣ (q + 2) ^ p - 1 := by
        have h1 : ((q + 2) ^ p : ℕ) ≡ 1 [MOD m'] := by
          rw [← ZMod.natCast_eq_natCast_iff]; push_cast
          have := pow_orderOf_eq_one ((q + 2 : ℕ) : ZMod m')
          rw [← hpdef] at this
          push_cast at this; exact this
        exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).mp h1.symm
      have hd2 : 2 ^ e ∣ (q + 2) ^ e := by
        rcases Nat.eq_zero_or_pos e with he | he
        · subst he; simp
        · apply pow_dvd_pow_of_dvd
          have : 2 ∣ q := by
            rw [hqe]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
          omega
      have hd := mul_dvd_mul hd2 hd1
      rw [← hqe, Nat.mul_sub_one, ← pow_add] at hd
      exact ((Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by omega) (by omega))).mpr hd).symm
    have hle : q - 1 ≤ p := hlb hper
    have htle : Nat.totient m' ≤ m' := Nat.totient_le m'
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      simp at hqe
      subst hqe
      have hlt := Nat.totient_lt q (by omega)
      have hphi : Nat.totient q = q - 1 := by omega
      refine ⟨(Nat.totient_eq_iff_prime (by omega)).mp hphi, ?_⟩
      rw [← cast_b q]; omega
    · exfalso
      have h2e : 2 ≤ 2 ^ e := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
      have : 2 * m' ≤ q := by rw [hqe]; exact Nat.mul_le_mul_right _ h2e
      have hq : q = 2 := by omega
      subst hq
      obtain ⟨k, hk, hdk⟩ := hnt 1
      apply hdk
      rw [digit_eq (by norm_num) (by norm_num)]
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      have h4 : 4 * 4 ^ j % 2 = 0 := by omega
      simp [pow_add, pow_one, h4]
  · rintro ⟨hprime, hord⟩
    have hq2 : q ≠ 2 := by
      rintro rfl
      have : (2 : ZMod 2) = 0 := rfl
      rw [this, orderOf_eq_zero_iff'.mpr] at hord
      · simp at hord
      · intro n hn; simp [zero_pow hn.ne']
    have hq3 : 3 ≤ q := by have := hprime.two_le; omega
    have hqpos : 0 < q := by omega
    have hpos : 0 < q - 1 := by omega
    have : Fact (1 < q) := ⟨by omega⟩
    have h1 : (2 : ZMod q) ^ (q - 1) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
    have hunit : IsUnit (2 : ZMod q) := IsUnit.of_pow_eq_one h1 hpos.ne'
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro K
      refine ⟨K, le_rfl, ?_⟩
      rw [digit_eq hqpos (by omega)]
      have hr : (q + 2) ^ K % q ≠ 0 := by
        intro h0
        have : (((q + 2) ^ K : ℕ) : ZMod q) = 0 := by
          rw [ZMod.natCast_eq_zero_iff]; exact Nat.dvd_of_mod_eq_zero h0
        push_cast at this
        rw [ZMod.natCast_self, zero_add] at this
        exact (hunit.pow K).ne_zero this
      have : q ≤ (q + 2) * ((q + 2) ^ K % q) := by nlinarith [Nat.pos_of_ne_zero hr]
      have : 1 ≤ (q + 2) * ((q + 2) ^ K % q) / q :=
        (Nat.le_div_iff_mul_le hqpos).mpr (by rw [one_mul]; exact this)
      omega
    · apply period_of_modeq (K := 0) hqpos (by omega) hpos
      rw [← ZMod.natCast_eq_natCast_iff]; push_cast
      rw [ZMod.natCast_self, zero_add, zero_add, h1, pow_zero]
    · rintro p ⟨hp, K, hK⟩
      have := hK K le_rfl
      rw [digit_eq hqpos (by omega), digit_eq hqpos (by omega)] at this
      have heq := rem_inj hqpos (by omega) this
      have hz : (((q + 2) ^ (K + p) : ℕ) : ZMod q) = (((q + 2) ^ K : ℕ) : ZMod q) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr heq
      push_cast at hz
      rw [ZMod.natCast_self, zero_add, pow_add] at hz
      have hp1 : (2 : ZMod q) ^ p = 1 :=
        (hunit.pow K).mul_left_cancel (by rw [hz, mul_one])
      rw [← hord]
      exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one hp1)

open Classical in
lemma count_shift (q : ℕ) : Nat.count InSeq (q + 2) = Nat.count PrimRoot2 q := by
  rw [Nat.add_comm, Nat.count_add]
  have h0 : Nat.count InSeq 2 = 0 := by
    rw [Nat.count_succ, Nat.count_succ, Nat.count_zero]
    simp [InSeq]
  rw [h0, zero_add]
  congr 1
  funext k
  rw [Nat.add_comm, inSeq_iff]

end OMA.P_a179194

open Classical in
theorem OMA.solution : type_of% @OMA.S_oeis_a179194.main := by
  intro n _ hne
  unfold OMA.S_oeis_a179194.A001122 at hne ⊢
  unfold OMA.S_oeis_a179194.a
  set q := Nat.nth OMA.S_oeis_a179194.PrimRoot2 (n - 1) with hq
  have hmem : OMA.S_oeis_a179194.PrimRoot2 q := Nat.nth_mem_of_ne_zero hne
  have hcount : Nat.count OMA.S_oeis_a179194.PrimRoot2 q = n - 1 :=
    Nat.count_nth (fun hf => Nat.lt_card_toFinset_of_nth_ne_zero hne hf)
  rw [← hcount, ← OMA.P_a179194.count_shift]
  exact Nat.nth_count ((OMA.P_a179194.inSeq_iff q).mpr hmem)
