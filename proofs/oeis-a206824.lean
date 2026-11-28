import OMAStatements.S_oeis_a206824

open OMA.S_oeis_a206824

namespace OMA.P_a206824

/-- Number of `j < N` with `N ∣ j (j + 1)`. -/
def f (N : ℕ) : ℕ := ((Finset.range N).filter (fun j => N ∣ j * (j + 1))).card

lemma dvd_iff_of_modEq {m x y : ℕ} (h : x ≡ y [MOD m]) :
    m ∣ x * (x + 1) ↔ m ∣ y * (y + 1) := by
  have h2 : x * (x + 1) ≡ y * (y + 1) [MOD m] := h.mul (h.add_right 1)
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨fun h' => h2.symm.trans h', fun h' => h2.trans h'⟩

lemma f_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (co : m.Coprime n) :
    f (m * n) = f m * f n := by
  unfold f
  rw [← Finset.card_product]
  apply Finset.card_nbij' (fun j => (j % m, j % n))
    (fun ab => (Nat.chineseRemainder co ab.1 ab.2 : ℕ))
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Finset.coe_product,
      Set.mem_prod] at hj ⊢
    refine ⟨⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hm), ?_⟩,
      ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hn), ?_⟩⟩
    · exact (dvd_iff_of_modEq (Nat.mod_modEq j m).symm).1 ((dvd_mul_right m n).trans hj.2)
    · exact (dvd_iff_of_modEq (Nat.mod_modEq j n).symm).1 ((dvd_mul_left n m).trans hj.2)
  · rintro ⟨x, y⟩ hxy
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Finset.coe_product,
      Set.mem_prod] at hxy ⊢
    have hc := (Nat.chineseRemainder co x y).2
    refine ⟨Nat.chineseRemainder_lt_mul co x y hm hn, ?_⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd co ((dvd_iff_of_modEq hc.1).2 hxy.1.2)
      ((dvd_iff_of_modEq hc.2).2 hxy.2.2)
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj
    have h := Nat.chineseRemainder_modEq_unique co (z := j) (Nat.mod_modEq j m).symm
      (Nat.mod_modEq j n).symm
    exact (h.eq_of_lt_of_lt hj.1 (Nat.chineseRemainder_lt_mul co _ _ hm hn)).symm
  · rintro ⟨x, y⟩ hxy
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq, Finset.coe_product,
      Set.mem_prod] at hxy
    have hc := (Nat.chineseRemainder co x y).2
    simp only [Prod.mk.injEq]
    exact ⟨Eq.trans hc.1 (Nat.mod_eq_of_lt hxy.1.1), Eq.trans hc.2 (Nat.mod_eq_of_lt hxy.2.1)⟩

lemma f_pp {p k : ℕ} (hp : p.Prime) (hk : 0 < k) : f (p ^ k) = 2 := by
  have h2 : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow hk.ne' p)
  unfold f
  have : (Finset.range (p ^ k)).filter (fun j => p ^ k ∣ j * (j + 1)) = {0, p ^ k - 1} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, hd⟩
      by_cases hpj : p ∣ j
      · left
        have hc : Nat.Coprime (p ^ k) (j + 1) := by
          apply Nat.Coprime.pow_left
          rw [hp.coprime_iff_not_dvd]
          intro h
          exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hpj).1 h))
        exact Nat.eq_zero_of_dvd_of_lt (hc.dvd_of_dvd_mul_right hd) hj
      · right
        have hc : Nat.Coprime (p ^ k) j :=
          Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).2 hpj)
        have := Nat.le_of_dvd (Nat.succ_pos j) (hc.dvd_of_dvd_mul_left hd)
        omega
    · rintro (rfl | rfl)
      · exact ⟨by omega, by simp⟩
      · refine ⟨by omega, ?_⟩
        rw [Nat.sub_add_cancel (by omega)]
        exact dvd_mul_left _ _
  rw [this, Finset.card_pair (by omega)]

lemma f_eq (N : ℕ) : N ≠ 0 → f N = 2 ^ N.primeFactors.card := by
  refine Nat.recOnPosPrimePosCoprime ?_ ?_ ?_ ?_ N
  · intro p k hp hk _
    rw [f_pp hp hk, Nat.primeFactors_prime_pow hk.ne' hp]
    simp
  · intro h; exact absurd rfl h
  · intro _; rw [Nat.primeFactors_one]; rfl
  · intro x y hx hy co ihx ihy _
    rw [f_mul (by omega) (by omega) co, ihx (by omega), ihy (by omega), co.primeFactors_mul,
      Finset.card_union_of_disjoint co.disjoint_primeFactors, pow_add]

lemma two_s (x : ℕ) : 2 * s x = x * (x + 1) := by
  unfold s
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self x).two_dvd

lemma cond_iff (n k : ℕ) : s k ≡ s n [MOD n] ↔ 2 * n ∣ (n + k) * (n + k + 1) := by
  have hk : (2:ℤ) * (s k : ℤ) = k * (k + 1) := by exact_mod_cast two_s k
  have hn : (2:ℤ) * (s n : ℤ) = n * (n + 1) := by exact_mod_cast two_s n
  rw [Nat.modEq_iff_dvd, ← Int.natCast_dvd_natCast,
    ← mul_dvd_mul_iff_left (a := (2:ℤ)) two_ne_zero]
  push_cast
  have e : ((n:ℤ) + k) * (n + k + 1) = -(2 * ((s n : ℤ) - s k)) + 2 * n * (n + 1 + k) := by
    rw [mul_sub, hk, hn]; ring
  rw [e, dvd_add_left (dvd_mul_right _ _), dvd_neg]

lemma reflect_iff {n j : ℕ} (hj : j < n) :
    2 * n ∣ (n - 1 - j) * (n - 1 - j + 1) ↔ 2 * n ∣ (n + j) * (n + j + 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, n = i + j + 1 := ⟨n - 1 - j, by omega⟩
  have h1 : i + j + 1 - 1 - j = i := by omega
  rw [h1, show (i + j + 1 + j) * (i + j + 1 + j + 1)
      = i * (i + 1) + 2 * (i + j + 1) * (2 * j + 1) by ring,
    Nat.dvd_add_left (dvd_mul_right _ _)]

lemma a_eq {n : ℕ} (hn : 0 < n) :
    2 * (a n + (if Odd n then 1 else 0)) = 2 ^ (2 * n).primeFactors.card := by
  set c : ℕ → ℕ := fun j => if 2 * n ∣ j * (j + 1) then 1 else 0 with hc
  have hf : f (2 * n) = ∑ j ∈ Finset.range (2 * n), c j := by
    rw [f, Finset.card_filter]
  have ha : a n = ∑ k ∈ Finset.Ico 1 n, c (n + k) := by
    rw [a, Finset.card_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hc, cond_iff]
  have hcn : c (n + 0) = if Odd n then 1 else 0 := by
    have : 2 * n ∣ (n + 0) * (n + 0 + 1) ↔ Odd n := by
      rw [Nat.add_zero, mul_comm (2:ℕ) n, Nat.mul_dvd_mul_iff_left hn, Nat.odd_iff,
        Nat.dvd_iff_mod_eq_zero]
      omega
    simp only [hc, this]
  have hsplit : ∑ j ∈ Finset.range n, c (n + j)
      = c (n + 0) + ∑ k ∈ Finset.Ico 1 n, c (n + k) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
  have hrefl : ∑ j ∈ Finset.range n, c j = ∑ j ∈ Finset.range n, c (n + j) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    simp only [hc, reflect_iff (Finset.mem_range.1 hj)]
  rw [← f_eq _ (by omega), hf, show 2 * n = n + n from two_mul n, Finset.sum_range_add, hrefl, hsplit, ← hcn, ← ha]
  ring

lemma even_clause {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    a n = 2 ^ (n.primeFactors.card - 1) := by
  have h := a_eq (n := n) (by omega)
  have hno : ¬ Odd n := Nat.not_odd_iff_even.2 he
  have h2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.2 ⟨Nat.prime_two, he.two_dvd, by omega⟩
  rw [Nat.primeFactors_mul two_ne_zero (by omega), Nat.prime_two.primeFactors,
    ← Finset.insert_eq, Finset.insert_eq_of_mem h2, if_neg hno] at h
  obtain ⟨m, hm⟩ : ∃ m, n.primeFactors.card = m + 1 :=
    ⟨n.primeFactors.card - 1, by have := Finset.card_pos.2 ⟨2, h2⟩; omega⟩
  rw [hm, pow_succ] at h
  rw [hm, Nat.add_sub_cancel]
  omega

lemma odd_clause {n : ℕ} (hn : 1 ≤ n) (ho : Odd n) :
    a n = 2 ^ n.primeFactors.card - 1 := by
  have h := a_eq (n := n) (by omega)
  have h2 : 2 ∉ n.primeFactors := by
    intro h2
    have := (Nat.mem_primeFactors.1 h2).2.1
    rw [Nat.odd_iff] at ho
    omega
  rw [Nat.primeFactors_mul two_ne_zero (by omega), Nat.prime_two.primeFactors,
    ← Finset.insert_eq, Finset.card_insert_of_notMem h2, if_pos ho, pow_succ] at h
  omega

lemma card_pf_prod (g : ℕ → ℕ) (hg : Function.Injective g) (m : ℕ) :
    (∏ i ∈ Finset.range m, Nat.nth Nat.Prime (g i)).primeFactors.card = m := by
  have hinj : Function.Injective (fun i => Nat.nth Nat.Prime (g i)) :=
    (Nat.nth_injective Nat.infinite_setOfPred_prime).comp hg
  have hpi : ∏ i ∈ Finset.range m, Nat.nth Nat.Prime (g i)
      = ∏ p ∈ (Finset.range m).image (fun i => Nat.nth Nat.Prime (g i)), p := by
    rw [Finset.prod_image (fun x _ y _ h => hinj h)]
  rw [hpi, Nat.primeFactors_prod,
    Finset.card_image_of_injective _ hinj, Finset.card_range]
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hp
  exact Nat.prime_nth_prime _

lemma Q_odd (m : ℕ) : Odd (∏ i ∈ Finset.range m, Nat.nth Nat.Prime (i + 1)) := by
  rw [Nat.odd_iff]
  have : ¬ 2 ∣ ∏ i ∈ Finset.range m, Nat.nth Nat.Prime (i + 1) := by
    intro h
    obtain ⟨i, _, hi⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).1 h
    have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Nat.prime_nth_prime _)).1 hi
    rw [← Nat.nth_prime_zero_eq_two] at h2
    exact absurd (Nat.nth_injective Nat.infinite_setOfPred_prime h2) (by omega)
  omega

lemma A002110_succ (m : ℕ) :
    A002110 (m + 1) = (∏ i ∈ Finset.range m, Nat.nth Nat.Prime (i + 1)) * 2 := by
  rw [A002110, Finset.prod_range_succ', Nat.nth_prime_zero_eq_two]

end OMA.P_a206824

open OMA.P_a206824 in
theorem OMA.solution : type_of% @OMA.S_oeis_a206824.main := by
  refine ⟨?_, ?_, fun n hn he => even_clause hn he, fun n hn ho => odd_clause (by omega) ho⟩
  · intro p e hp he
    have h2 : 2 ≤ p ^ e := le_trans hp.two_le (Nat.le_self_pow he.ne' p)
    have hω : (p ^ e).primeFactors.card = 1 := by
      rw [Nat.primeFactors_prime_pow he.ne' hp, Finset.card_singleton]
    rcases hp.eq_two_or_odd' with rfl | hodd
    · rw [even_clause h2 ((Nat.even_pow' he.ne').2 even_two), hω]; norm_num
    · rw [odd_clause (by omega) (hodd.pow), hω]; norm_num
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hQ := Q_odd m
    have hQpos : 1 ≤ ∏ i ∈ Finset.range m, Nat.nth Nat.Prime (i + 1) := by
      rw [Nat.odd_iff] at hQ; omega
    have hω : (A002110 (m + 1)).primeFactors.card = m + 1 := by
      rw [A002110]; exact card_pf_prod id Function.injective_id (m + 1)
    have hP2 : 2 ≤ A002110 (m + 1) := by rw [A002110_succ]; omega
    have hPe : Even (A002110 (m + 1)) := by
      rw [A002110_succ]; exact even_iff_two_dvd.2 (dvd_mul_left _ _)
    refine ⟨?_, ?_⟩
    · rw [even_clause hP2 hPe, hω]
    · rw [A002110_succ, Nat.mul_div_cancel _ two_pos, odd_clause hQpos hQ,
        card_pf_prod (· + 1) (fun x y h => by simpa using h) m, Nat.add_sub_cancel]
