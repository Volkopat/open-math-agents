import OMAStatements.S_oeis_a098275

-- Credit: @EmadY
-- Proof of Chapoton's conjecture on OEIS A098275: (n + 1) divides a(n) for all n.

private lemma chap_choose_add_eq_sum (n i j : ℕ) (hi : i ≤ n) :
    (i + j).choose i = ∑ k ∈ Finset.range (n + 1), i.choose k * j.choose k := by
  rw [add_comm i j, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => j.choose a * i.choose b)]
  refine (Finset.sum_congr rfl fun k hk => ?_).trans
    (Finset.sum_subset (Finset.range_mono (by lia : i + 1 ≤ n + 1)) fun k _ hk => ?_)
  · simp only [Finset.mem_range] at hk
    rw [Nat.choose_symm (by lia : k ≤ i), mul_comm]
  · simp only [Finset.mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by lia : i < k), zero_mul]

private lemma chap_sum_choose_mul_choose (n k : ℕ) (hk : k ≤ n) (g : ℕ → ℕ) :
    ∑ m ∈ Finset.range (n + 1), g m * (n.choose m * m.choose k) =
      n.choose k * ∑ t ∈ Finset.range (n - k + 1), g (k + t) * (n - k).choose t := by
  rw [← Finset.sum_range_add_sum_Ico _ (by lia : k ≤ n + 1)]
  have h0 : ∑ m ∈ Finset.range k, g m * (n.choose m * m.choose k) = 0 :=
    Finset.sum_eq_zero fun m hm => by
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hm), mul_zero, mul_zero]
  rw [h0, zero_add, Finset.sum_Ico_eq_sum_range, show n + 1 - k = n - k + 1 by lia, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Nat.choose_mul (Nat.le_add_right k t), Nat.add_sub_cancel_left]
  ring

private lemma chap_sum_j (n k : ℕ) (hk : k ≤ n) :
    ∑ j ∈ Finset.range (n + 1), n.choose j ^ 2 * j.choose k =
      n.choose k * (2 * n - k).choose n := by
  have h1 : ∑ j ∈ Finset.range (n + 1), n.choose j ^ 2 * j.choose k =
      ∑ j ∈ Finset.range (n + 1), n.choose j * (n.choose j * j.choose k) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [h1, chap_sum_choose_mul_choose n k hk]
  congr 1
  rw [show 2 * n - k = n - k + n by lia, ← Nat.choose_symm_add, Nat.add_choose_eq,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => (n - k).choose a * n.choose b)]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_range] at ht
  rw [show n - k - t = n - (k + t) by lia, Nat.choose_symm (by lia : k + t ≤ n), mul_comm]

private lemma chap_sum_i (n k : ℕ) (hk : k ≤ n) :
    ∑ i ∈ Finset.range (n + 1), n.choose i ^ 2 * (n + i).choose n * i.choose k =
      n.choose k * ∑ r ∈ Finset.range (n - k + 1),
        n.choose r * (2 * n - r).choose n * (n - k).choose r := by
  have h1 : ∑ i ∈ Finset.range (n + 1), n.choose i ^ 2 * (n + i).choose n * i.choose k =
      ∑ i ∈ Finset.range (n + 1), (n.choose i * (n + i).choose n) * (n.choose i * i.choose k) :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [h1, chap_sum_choose_mul_choose n k hk]
  congr 1
  rw [← Finset.sum_range_reflect
    (fun t => n.choose (k + t) * (n + (k + t)).choose n * (n - k).choose t) (n - k + 1)]
  refine Finset.sum_congr rfl fun r hr => ?_
  simp only [Finset.mem_range] at hr
  rw [show k + (n - k + 1 - 1 - r) = n - r by lia,
    show n - k + 1 - 1 - r = n - k - r by lia,
    show n + (n - r) = 2 * n - r by lia,
    Nat.choose_symm (by lia : r ≤ n), Nat.choose_symm (by lia : r ≤ n - k)]

private lemma chap_a_eq (n : ℕ) :
    OMA.S_oeis_a098275.a n =
      ∑ k ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n - k + 1),
        n.choose k * n.choose r * n.choose (k + r) *
          ((k + r).choose k * (2 * n - k).choose n * (2 * n - r).choose n) := by
  calc OMA.S_oeis_a098275.a n
    _ = ∑ i ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (n.choose i ^ 2 * (n + i).choose n * i.choose k) *
            ∑ j ∈ Finset.range (n + 1), n.choose j ^ 2 * j.choose k := by
      unfold OMA.S_oeis_a098275.a
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      trans ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        (n.choose i ^ 2 * (n + i).choose n * i.choose k) * (n.choose j ^ 2 * j.choose k)
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [chap_choose_add_eq_sum n i j (by lia), Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ k ∈ Finset.range (n + 1),
          (∑ i ∈ Finset.range (n + 1), n.choose i ^ 2 * (n + i).choose n * i.choose k) *
            (∑ j ∈ Finset.range (n + 1), n.choose j ^ 2 * j.choose k) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_range] at hk
      rw [chap_sum_i n k (by lia), chap_sum_j n k (by lia), mul_assoc, Finset.sum_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hmul : n.choose k * (n - k).choose r = n.choose (k + r) * (k + r).choose k := by
        rw [Nat.choose_mul (Nat.le_add_right k r), Nat.add_sub_cancel_left]
      calc n.choose k * (n.choose r * (2 * n - r).choose n * (n - k).choose r *
            (n.choose k * (2 * n - k).choose n))
        _ = (n.choose k * (n - k).choose r) *
              (n.choose k * n.choose r * (2 * n - k).choose n * (2 * n - r).choose n) := by ring
        _ = _ := by rw [hmul]; ring

private lemma chap_dvd_term (n k r : ℕ) (hkr : k + r ≤ n) :
    (n + 1) ∣ (k + r).choose k * (2 * n - k).choose n * (2 * n - r).choose n := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p m hp hpm
  have : Fact p.Prime := ⟨hp⟩
  have hc1 : (k + r).choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hc2 : (2 * n - k).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hc3 : (2 * n - r).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [padicValNat_dvd_iff_le (mul_ne_zero (mul_ne_zero hc1 hc2) hc3),
    padicValNat.mul (mul_ne_zero hc1 hc2) hc3, padicValNat.mul hc1 hc2]
  let B := max (m + 1) (Nat.log p (2 * n) + 1)
  have hlog : ∀ x ≤ 2 * n, Nat.log p x < B := fun x hx =>
    (Nat.log_mono_right hx).trans_lt ((Nat.lt_add_one _).trans_le (le_max_right _ _))
  rw [padicValNat_choose (by omega) (hlog _ (by omega)),
    padicValNat_choose (by omega) (hlog _ (by omega)),
    padicValNat_choose (by omega) (hlog _ (by omega))]
  suffices hsub : Finset.Ico 1 (m + 1) ⊆
      Finset.filter (fun i => p ^ i ≤ k % p ^ i + (k + r - k) % p ^ i) (Finset.Ico 1 B) ∪
      Finset.filter (fun i => p ^ i ≤ n % p ^ i + (2 * n - k - n) % p ^ i) (Finset.Ico 1 B) ∪
      Finset.filter (fun i => p ^ i ≤ n % p ^ i + (2 * n - r - n) % p ^ i) (Finset.Ico 1 B) by
    calc m = (Finset.Ico 1 (m + 1)).card := by simp
      _ ≤ _ := (Finset.card_le_card hsub).trans
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  intro s hs
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico] at hs ⊢
  have hsB : 1 ≤ s ∧ s < B := ⟨hs.1, hs.2.trans_le (le_max_left _ _)⟩
  rw [Nat.add_sub_cancel_left, show 2 * n - k - n = n - k by omega,
    show 2 * n - r - n = n - r by omega]
  have hq2 : 2 ≤ p ^ s :=
    hp.two_le.trans ((Nat.pow_one p).symm.le.trans (Nat.pow_le_pow_right hp.pos hs.1))
  obtain ⟨_ | c, hc⟩ := dvd_trans (Nat.pow_dvd_pow p (by omega : s ≤ m)) hpm
  · omega
  rw [Nat.mul_succ] at hc
  have hn_mod : n % p ^ s = p ^ s - 1 := by
    rw [show n = p ^ s - 1 + p ^ s * c by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  by_cases hnk : (n - k) % p ^ s = 0
  · by_cases hnr : (n - r) % p ^ s = 0
    · refine Or.inl (Or.inl ⟨hsB, ?_⟩)
      have hnk_eq : n = k + p ^ s * ((n - k) / p ^ s) := by
        have := Nat.div_add_mod (n - k) (p ^ s); omega
      have hnr_eq : n = r + p ^ s * ((n - r) / p ^ s) := by
        have := Nat.div_add_mod (n - r) (p ^ s); omega
      have hk_mod : k % p ^ s = p ^ s - 1 := by rw [← hn_mod, hnk_eq, Nat.add_mul_mod_self_left]
      have hr_mod : r % p ^ s = p ^ s - 1 := by rw [← hn_mod, hnr_eq, Nat.add_mul_mod_self_left]
      omega
    · refine Or.inr ⟨hsB, ?_⟩
      rw [hn_mod]
      exact (Nat.sub_add_cancel (by omega)).symm.le.trans
        (Nat.add_le_add_left (Nat.pos_of_ne_zero hnr) _)
  · refine Or.inl (Or.inr ⟨hsB, ?_⟩)
    rw [hn_mod]
    exact (Nat.sub_add_cancel (by omega)).symm.le.trans
      (Nat.add_le_add_left (Nat.pos_of_ne_zero hnk) _)

theorem OMA.solution : type_of% @OMA.S_oeis_a098275.main := by
  intro n
  rw [chap_a_eq]
  refine Finset.dvd_sum fun k hk => Finset.dvd_sum fun r hr => ?_
  rw [Finset.mem_range] at hk hr
  exact dvd_mul_of_dvd_right (chap_dvd_term n k r (by omega)) _
