import OMAStatements.S_oeis_a343073
import Mathlib


namespace A343073Sol

open OMA.S_oeis_a343073

lemma tet_succ (b x : ℕ) : tet b (x + 1) = b ^ tet b x := rfl

lemma tet_one (b : ℕ) : tet b 1 = b := by
  show b ^ 1 = b
  exact pow_one b

lemma tet_pos (b : ℕ) (hb : 0 < b) : ∀ x, 0 < tet b x
  | 0 => by show 0 < 1; exact Nat.one_pos
  | x + 1 => by rw [tet_succ]; exact pow_pos hb _

lemma coprime_of_mem (n b x : ℕ) (hb : 0 < b) (hx : 1 ≤ x) (h : tet b x ≡ 1 [MOD n]) :
    Nat.Coprime b n := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [tet_succ] at h
  have h1 : Nat.Coprime (b ^ tet b y) n := by
    have := Nat.ModEq.gcd_eq h
    rw [Nat.Coprime, this]
    simp
  exact (Nat.coprime_pow_left_iff (tet_pos b hb y) b n).mp h1

lemma not_mem (n b m : ℕ) (hb1 : ¬ b ≡ 1 [MOD n]) (hm : b ^ m ≡ 1 [MOD n])
    (hcop : Nat.Coprime b m) : ∀ x, 1 ≤ x → ¬ tet b x ≡ 1 [MOD n] := by
  have key : ∀ k : ℕ, b ^ k ≡ 1 [MOD n] → ((b : ZMod n)) ^ k = 1 := by
    intro k hk
    have := (ZMod.natCast_eq_natCast_iff (b ^ k) 1 n).mpr hk
    simpa using this
  intro x hx h
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rcases y with _ | y
  · rw [tet_one] at h
    exact hb1 h
  · rw [tet_succ, tet_succ] at h
    have hE : Nat.Coprime (b ^ tet b y) m := Nat.Coprime.pow_left _ hcop
    have h3 := pow_gcd_eq_one.mpr ⟨key _ h, key _ hm⟩
    rw [Nat.Coprime.gcd_eq_one hE, pow_one] at h3
    apply hb1
    have h4 : ((b : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      rw [Nat.cast_one]
      exact h3
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h4

lemma witness (n : ℕ) (hn : 4 ≤ n) : ∃ q, Nat.Prime q ∧ 2 < q ∧ q < n ∧ n < 2 * q := by
  obtain ⟨q, hq, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  have hodd := hq.eq_two_or_odd
  refine ⟨q, hq, ?_, ?_, ?_⟩ <;> omega

lemma lt_totient (n : ℕ) (hn : 4 ≤ n) : a n < Nat.totient n := by
  obtain ⟨q, hq, hq2, hqn, hnq⟩ := witness n hn
  have hqndvd : ¬ q ∣ n := by
    rintro ⟨c, hc⟩
    rcases Nat.lt_or_ge c 2 with h | h
    · interval_cases c <;> omega
    · nlinarith
  have htot_lt : Nat.totient n < n := Nat.totient_lt n (by omega)
  have htot_pos : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
  have htot_even : Even (Nat.totient n) := Nat.totient_even (by omega)
  have hqndvd2 : ¬ q ∣ Nat.totient n := by
    rintro ⟨c, hc⟩
    rcases Nat.lt_or_ge c 2 with h | h
    · interval_cases c
      · omega
      · obtain ⟨r, hr⟩ := htot_even
        have := hq.eq_two_or_odd
        omega
    · nlinarith
  have hcopn : Nat.Coprime q n := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqndvd
  have hcopt : Nat.Coprime q (Nat.totient n) := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqndvd2
  have hq1 : ¬ q ≡ 1 [MOD n] := by
    intro h
    unfold Nat.ModEq at h
    rw [Nat.mod_eq_of_lt hqn, Nat.mod_eq_of_lt (by omega)] at h
    omega
  let T : Finset ℕ := (Finset.range n).filter n.Coprime
  have hsub : {b : ℕ | 0 < b ∧ b < n ∧ ∃ x : ℕ, 1 ≤ x ∧ tet b x ≡ 1 [MOD n]} ⊆ (T : Set ℕ) := by
    intro b hb
    obtain ⟨hb0, hbn, x, hx, hxb⟩ := hb
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨hbn, (coprime_of_mem n b x hb0 hx hxb).symm⟩
  have hq_in : q ∈ (T : Set ℕ) := by
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨hqn, hcopn.symm⟩
  have hq_out : q ∉ {b : ℕ | 0 < b ∧ b < n ∧ ∃ x : ℕ, 1 ≤ x ∧ tet b x ≡ 1 [MOD n]} := by
    rintro ⟨_, _, x, hx, hxq⟩
    exact not_mem n q (Nat.totient n) hq1 (Nat.ModEq.pow_totient hcopn) hcopt x hx hxq
  have hss : {b : ℕ | 0 < b ∧ b < n ∧ ∃ x : ℕ, 1 ≤ x ∧ tet b x ≡ 1 [MOD n]} ⊂ (T : Set ℕ) :=
    (Set.ssubset_iff_of_subset hsub).mpr ⟨q, hq_in, hq_out⟩
  have hlt := Set.ncard_lt_ncard hss (Finset.finite_toSet T)
  rw [Set.ncard_coe_finset] at hlt
  unfold a
  rw [Nat.totient_eq_card_coprime]
  exact hlt

lemma a_two : a 2 = 1 := by
  have h : {b : ℕ | 0 < b ∧ b < 2 ∧ ∃ x : ℕ, 1 ≤ x ∧ tet b x ≡ 1 [MOD 2]} = {1} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, _⟩
      omega
    · rintro rfl
      exact ⟨by norm_num, by norm_num, 1, le_rfl, by decide⟩
  unfold a
  rw [h, Set.ncard_singleton]

lemma a_three : a 3 = 2 := by
  have h : {b : ℕ | 0 < b ∧ b < 3 ∧ ∃ x : ℕ, 1 ≤ x ∧ tet b x ≡ 1 [MOD 3]} = {1, 2} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, _⟩
      omega
    · rintro (rfl | rfl)
      · exact ⟨by norm_num, by norm_num, 1, le_rfl, by decide⟩
      · exact ⟨by norm_num, by norm_num, 2, by norm_num, by decide⟩
  unfold a
  rw [h, Set.ncard_pair (by norm_num)]

end A343073Sol

theorem OMA.solution : type_of% @OMA.S_oeis_a343073.main := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h2, h⟩
    by_contra hne
    have h4 : 4 ≤ n := by omega
    have := A343073Sol.lt_totient n h4
    omega
  · rintro (rfl | rfl)
    · exact ⟨le_rfl, by rw [A343073Sol.a_two]; decide⟩
    · exact ⟨by norm_num, by rw [A343073Sol.a_three]; decide⟩

