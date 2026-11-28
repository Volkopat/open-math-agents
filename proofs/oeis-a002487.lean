import OMAStatements.S_oeis_a002487

namespace OMA.CalkinWilfFrequency

open OMA.S_oeis_a002487

private theorem a_even (k : ℕ) : a (2 * k) = a k := by
  by_cases h : k = 0
  · subst k
    rfl
  have hk : 2 * k = (2 * k - 2) + 2 := by omega
  conv_lhs => rw [hk, a.eq_3]
  split
  · congr 1
    omega
  · omega

private theorem a_odd (k : ℕ) : a (2 * k + 1) = a k + a (k + 1) := by
  by_cases h : k = 0
  · subst k
    norm_num [a.eq_1, a.eq_2]
  have hk : 2 * k + 1 = (2 * k - 1) + 2 := by omega
  conv_lhs => rw [hk, a.eq_3]
  split
  · omega
  · have hhalf : ((2 * k - 1) + 2) / 2 = k := by omega
    rw [hhalf]

private theorem a_odd_next (k : ℕ) : a (2 * k + 1 + 1) = a (k + 1) := by
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, a_even]

private def Row (d k : ℕ) : Prop := 2 ^ d ≤ k ∧ k < 2 ^ (d + 1)

private theorem row_one : Row 0 1 := by unfold Row; decide

private theorem row_pos {d k : ℕ} (hk : Row d k) : 0 < k :=
  (Nat.pow_pos (by decide)).trans_le hk.1

private theorem row_left {d k : ℕ} (hk : Row d k) : Row (d + 1) (2 * k) := by
  rcases hk with ⟨h₁, h₂⟩
  constructor <;> rw [pow_succ] <;> omega

private theorem row_right {d k : ℕ} (hk : Row d k) : Row (d + 1) (2 * k + 1) := by
  rcases hk with ⟨h₁, h₂⟩
  constructor <;> rw [pow_succ] <;> omega

private theorem pair_valid (k : ℕ) (hk : 0 < k) :
    0 < a k ∧ 0 < a (k + 1) ∧ (a k).Coprime (a (k + 1)) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases he : k = 1
    · subst k
      norm_num [a.eq_2, a_even 1]
    have hparent := ih (k / 2) (by omega) (by omega : 0 < k / 2)
    by_cases h : k % 2 = 0
    · obtain ⟨hp, hq, hc⟩ := hparent
      rw [show k = 2 * (k / 2) by omega, a_even, a_odd]
      exact ⟨hp, by omega, Nat.coprime_self_add_right.mpr hc⟩
    · obtain ⟨hp, hq, hc⟩ := hparent
      rw [show k = 2 * (k / 2) + 1 by omega, a_odd, a_odd_next]
      exact ⟨by omega, hq, Nat.coprime_add_self_left.mpr hc⟩

private theorem pair_order (k : ℕ) (hk : 1 < k) :
    if k % 2 = 0 then a k < a (k + 1) else a (k + 1) < a k := by
  obtain ⟨hp, hq, _⟩ := pair_valid (k / 2) (by omega)
  split
  · rename_i h
    rw [show k = 2 * (k / 2) by omega, a_even, a_odd]
    omega
  · rename_i h
    rw [show k = 2 * (k / 2) + 1 by omega, a_odd, a_odd_next]
    omega

private theorem pair_unique (i j : ℕ) (hi : 0 < i) (hj : 0 < j)
    (h₁ : a i = a j) (h₂ : a (i + 1) = a (j + 1)) : i = j := by
  induction i using Nat.strong_induction_on generalizing j with
  | h i ih =>
    by_cases hi₁ : i = 1
    · subst i
      by_contra hn
      have he : a j = a (j + 1) := by
        rw [← h₁, ← h₂, show 1 + 1 = 2 * 1 by decide, a_even]
      have h := pair_order j (by omega)
      split at h <;> omega
    by_cases hj₁ : j = 1
    · subst j
      have he : a i = a (i + 1) := by
        rw [h₁, h₂, show 1 + 1 = 2 * 1 by decide, a_even]
      have h := pair_order i (by omega)
      split at h <;> omega
    have hoi := pair_order i (by omega)
    have hoj := pair_order j (by omega)
    by_cases ei : i % 2 = 0 <;> by_cases ej : j % 2 = 0
    · rw [show i = 2 * (i / 2) by omega, show j = 2 * (j / 2) by omega,
          a_even, a_even] at h₁
      rw [show i = 2 * (i / 2) by omega, show j = 2 * (j / 2) by omega,
          a_odd, a_odd] at h₂
      have hh := ih (i / 2) (by omega) (j / 2) (by omega) (by omega) h₁ (by omega)
      omega
    · simp [ei] at hoi
      simp [ej] at hoj
      omega
    · simp [ei] at hoi
      simp [ej] at hoj
      omega
    · rw [show i = 2 * (i / 2) + 1 by omega, show j = 2 * (j / 2) + 1 by omega,
          a_odd, a_odd] at h₁
      rw [show i = 2 * (i / 2) + 1 by omega, show j = 2 * (j / 2) + 1 by omega,
          a_odd_next, a_odd_next] at h₂
      have hh := ih (i / 2) (by omega) (j / 2) (by omega) (by omega) (by omega) h₂
      omega

/-- Subtractive Euclid reaches every positive coprime pair and gives a depth bound. -/
private theorem pair_exists (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (hc : u.Coprime v) :
    ∃ d k, d < max u v ∧ Row d k ∧ a k = u ∧ a (k + 1) = v := by
  generalize hmax : max u v = b
  induction b using Nat.strong_induction_on generalizing u v with
  | h b ih =>
    rcases lt_trichotomy u v with h | h | h
    · have hlt : max u (v - u) < b := by
        rw [← hmax, max_eq_right h.le]
        exact max_lt_iff.mpr ⟨h, by omega⟩
      obtain ⟨d, k, hd, hk, hku, hkv⟩ :=
        ih _ hlt u (v - u) hu (by omega) ((Nat.coprime_sub_self_right h.le).mpr hc) rfl
      refine ⟨d + 1, 2 * k, by omega, row_left hk, (a_even k).trans hku, ?_⟩
      rw [a_odd, hku, hkv]
      omega
    · subst v
      have hu₁ : u = 1 := by simpa using hc
      subst u
      exact ⟨0, 1, by simpa using hmax.symm ▸ (show 0 < max 1 1 by decide), row_one,
        a.eq_2, (a_even 1).trans a.eq_2⟩
    · have hlt : max (u - v) v < b := by
        rw [← hmax, max_eq_left h.le]
        exact max_lt_iff.mpr ⟨by omega, h⟩
      obtain ⟨d, k, hd, hk, hku, hkv⟩ :=
        ih _ hlt (u - v) v (by omega) hv ((Nat.coprime_sub_self_left h.le).mpr hc) rfl
      refine ⟨d + 1, 2 * k + 1, by omega, row_right hk, ?_, (a_odd_next k).trans hkv⟩
      rw [a_odd, hku, hkv]
      omega

/-- Read an extra run of zero bits along the left branch. -/
private theorem pair_lift (i d q : ℕ) (hi : Row d i) :
    Row (d + q) (2 ^ q * i) ∧ a (2 ^ q * i) = a i ∧
      a (2 ^ q * i + 1) = a (i + 1) + q * a i := by
  induction q with
  | zero => simpa using hi
  | succ q ih =>
    rw [pow_succ', mul_assoc]
    refine ⟨row_left ih.1, (a_even _).trans ih.2.1, ?_⟩
    rw [a_odd, ih.2.1, ih.2.2, Nat.succ_mul]
    omega

private theorem residue_injective_ordered {d i j : ℕ} (hi : Row d i) (hj : Row d j)
    (hfirst : a i = a j) (hmod : a (i + 1) % a i = a (j + 1) % a j)
    (horder : a (i + 1) ≤ a (j + 1)) : i = j := by
  let q := a (j + 1) / a i - a (i + 1) / a i
  have hle : a (i + 1) / a i ≤ a (j + 1) / a i := Nat.div_le_div_right horder
  have hdiff : a (i + 1) + q * a i = a (j + 1) := by
    have hq : q + a (i + 1) / a i = a (j + 1) / a i := Nat.sub_add_cancel hle
    have hq' := congrArg (fun t => a i * t) hq
    rw [Nat.mul_add] at hq'
    have ha := Nat.mod_add_div (a (i + 1)) (a i)
    have hb := Nat.mod_add_div (a (j + 1)) (a i)
    rw [← hfirst] at hmod
    rw [hmod] at ha
    rw [Nat.mul_comm q]
    omega
  obtain ⟨hl, hl₁, hl₂⟩ := pair_lift i d q hi
  have heq := pair_unique _ _ (row_pos hl) (row_pos hj) (hl₁.trans hfirst) (hl₂.trans hdiff)
  have hq : q = 0 := by
    by_contra hn
    have hpow : 2 ≤ 2 ^ q := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 1 ≤ q)
    have hlow : 2 ^ (d + 1) ≤ 2 ^ q * i := by
      simpa [pow_succ'] using Nat.mul_le_mul hpow hi.1
    rw [heq] at hlow
    exact (not_le_of_gt hj.2) hlow
  simpa [hq] using heq

private theorem residue_injective {d i j : ℕ} (hi : Row d i) (hj : Row d j)
    (hfirst : a i = a j) (hmod : a (i + 1) % a i = a (j + 1) % a j) : i = j := by
  rcases le_total (a (i + 1)) (a (j + 1)) with h | h
  · exact residue_injective_ordered hi hj hfirst hmod h
  · exact (residue_injective_ordered hj hi hfirst.symm hmod.symm h).symm

private theorem residue_exists {d n b : ℕ} (hn : 0 < n) (hd : n ≤ d + 1)
    (hbn : b < n) (hc : n.Coprime b) :
    ∃ k, Row d k ∧ a k = n ∧ a (k + 1) % a k = b := by
  by_cases h₁ : n = 1
  · subst n
    have hb : b = 0 := by omega
    obtain ⟨hk, hleft, _⟩ := pair_lift 1 0 d row_one
    refine ⟨2 ^ d * 1, by simpa using hk, hleft.trans a.eq_2, ?_⟩
    rw [hleft, a.eq_2, Nat.mod_one, hb]
  have hb : 0 < b := by
    by_contra! hz
    have he : b = 0 := by omega
    rw [he] at hc
    exact h₁ (by simpa using hc)
  obtain ⟨e, i, he, hi, hleft, hright⟩ := pair_exists n b hn hb hc
  rw [max_eq_left hbn.le] at he
  obtain ⟨hk, hkl, hkr⟩ := pair_lift i e (d - e) hi
  refine ⟨2 ^ (d - e) * i, ?_, hkl.trans hleft, ?_⟩
  · rwa [show e + (d - e) = d by omega] at hk
  · rw [hkr, hkl, hleft, hright, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hbn]

theorem frequency (m n : ℕ) (hn : 1 ≤ n) (hm : n ≤ m) :
    ((Finset.Icc (2 ^ (m - 1)) (2 ^ m - 1)).filter fun k => a k = n).card = Nat.totient n := by
  let d := m - 1
  have hdm : m = d + 1 := by dsimp [d]; omega
  rw [Nat.totient_eq_card_coprime]
  have hrow (k : ℕ) : k ∈ Finset.Icc (2 ^ d) (2 ^ m - 1) ↔ Row d k := by
    rw [Finset.mem_Icc]
    unfold Row
    rw [← hdm]
    have hpow : 0 < (2 : ℕ) ^ m := Nat.pow_pos (by decide)
    omega
  change ((Finset.Icc (2 ^ d) (2 ^ m - 1)).filter fun k => a k = n).card = _
  refine Finset.card_bij (fun k _ => a (k + 1) % a k) ?_ ?_ ?_
  · intro k hk
    obtain ⟨hki, hkn⟩ := Finset.mem_filter.mp hk
    have hkr := (hrow k).mp hki
    have hc := (pair_valid k (row_pos hkr)).2.2
    rw [Finset.mem_filter, Finset.mem_range, ← hkn]
    exact ⟨Nat.mod_lt _ (by omega), by rw [Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec]; exact hc⟩
  · intro i hi j hj h
    obtain ⟨hi₁, hi₂⟩ := Finset.mem_filter.mp hi
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_filter.mp hj
    exact residue_injective ((hrow i).mp hi₁) ((hrow j).mp hj₁) (hi₂.trans hj₂.symm) h
  · intro b hb
    obtain ⟨hbn, hc⟩ := Finset.mem_filter.mp hb
    obtain ⟨k, hk, hkn, hkb⟩ :=
      residue_exists (d := d) hn (by omega) (Finset.mem_range.mp hbn) hc
    exact ⟨k, Finset.mem_filter.mpr ⟨(hrow k).mpr hk, hkn⟩, hkb⟩

end OMA.CalkinWilfFrequency

theorem OMA.solution : type_of% @OMA.S_oeis_a002487.main :=
  OMA.CalkinWilfFrequency.frequency
