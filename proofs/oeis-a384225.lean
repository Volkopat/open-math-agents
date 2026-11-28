import OMAStatements.S_oeis_a384225

-- Problem: A384225: Irregular triangle read by rows: T(n,k) is the number of odd numbers in the k-th 2-dense sublist of divisors of n, with n >= 1, k 
-- Upstream: formal-conjectures statements/oeis-a384225.lean:0 (declaration OMA.S_oeis_a384225.main)
-- Credit: @thtsben2 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a384225

private lemma mem_of_mem_splitBy {α : Type*} {r : α → α → Bool} {L b : List α}
    (hb : b ∈ L.splitBy r) {x : α} (hx : x ∈ b) : x ∈ L := by
  rw [← List.flatten_splitBy r L]
  exact List.mem_flatten.mpr ⟨b, hb, hx⟩

private lemma nodup_of_mem_splitBy {α : Type*} {r : α → α → Bool} {L b : List α}
    (hL : L.Nodup) (hb : b ∈ L.splitBy r) : b.Nodup := by
  rw [← List.flatten_splitBy r L] at hL
  exact (List.nodup_flatten.mp hL).1 b hb

private lemma pairwise_le_of_mem_splitBy {r : ℕ → ℕ → Bool} {L b : List ℕ}
    (hL : L.Pairwise (· ≤ ·)) (hb : b ∈ L.splitBy r) : b.Pairwise (· ≤ ·) := by
  rw [← List.flatten_splitBy r L] at hL
  exact (List.pairwise_flatten.mp hL).1 b hb

private lemma head_le_of_pairwise {L : List ℕ} (hL : L.Pairwise (· ≤ ·))
    (hne : L ≠ []) {x : ℕ} (hx : x ∈ L) : L.head hne ≤ x := by
  cases L with
  | nil => contradiction
  | cons a t =>
    simp only [List.head_cons]
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact le_rfl
    · exact (List.pairwise_cons.mp hL).1 x hxt

private lemma le_getLast_of_pairwise {L : List ℕ} (hL : L.Pairwise (· ≤ ·))
    (hne : L ≠ []) {x : ℕ} (hx : x ∈ L) : x ≤ L.getLast hne := by
  induction L generalizing x with
  | nil => contradiction
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [List.getLast_singleton]
      simp only [List.mem_singleton] at hx
      rw [hx]
    | cons b t =>
      rw [List.getLast_cons (List.cons_ne_nil b t)]
      have ht_pw : (b :: t).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hL).2
      rcases List.mem_cons.mp hx with rfl | hxt
      · exact ((List.pairwise_cons.mp hL).1 b List.mem_cons_self).trans
          (ih ht_pw (List.cons_ne_nil b t) List.mem_cons_self)
      · exact ih ht_pw (List.cons_ne_nil b t) hxt

private lemma splitBy_closed {L : List ℕ} (hL : L.Pairwise (· ≤ ·)) :
    let r := fun d e : ℕ => decide (e ≤ 2 * d)
    ∀ b ∈ L.splitBy r, ∀ x ∈ b, ∀ y ∈ L, y ≤ 2 * x → x ≤ 2 * y → y ∈ b := by
  intro r b hb x hx y hy hyx hxy
  set S := L.splitBy r
  have hchain : S.IsChain fun a c => ∃ ha hc, r (a.getLast ha) (c.head hc) = false :=
    List.isChain_getLast_head_splitBy r L
  have hchain_get := List.isChain_iff_getElem.mp hchain
  have hadj : ∀ i (hi : i + 1 < S.length),
      ∀ u ∈ S[i], ∀ v ∈ S[i + 1], 2 * u < v := by
    intro i hi u hu v hv
    obtain ⟨ha, hc, hfalse⟩ := hchain_get i hi
    have hlt : 2 * S[i].getLast ha < S[i + 1].head hc := by
      simpa [r] using hfalse
    have hu_le : u ≤ S[i].getLast ha :=
      le_getLast_of_pairwise (pairwise_le_of_mem_splitBy hL (List.getElem_mem _)) ha hu
    have hv_le : S[i + 1].head hc ≤ v :=
      head_le_of_pairwise (pairwise_le_of_mem_splitBy hL (List.getElem_mem _)) hc hv
    omega
  have hne : ∀ i (hi : i < S.length), S[i] ≠ [] :=
    fun i hi => List.ne_nil_of_mem_splitBy (List.getElem_mem hi)
  have hlt_all : ∀ i j (hij : i < j) (hj : j < S.length),
      ∀ u ∈ S[i], ∀ v ∈ S[j], 2 * u < v := by
    intro i j hij hj
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    induction d generalizing i with
    | zero =>
      simpa using hadj i hj
    | succ d ih =>
      intro u hu v hv
      have hi1 : i + 1 < i + d + 1 + 1 := by omega
      have hmid_ne : S[i + d + 1] ≠ [] := hne (i + d + 1) (by omega)
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hmid_ne
      have h1 : 2 * u < w := ih i (by omega) (by omega) u hu w hw
      have h2 : 2 * w < v := hadj (i + d + 1) hj w hw v hv
      omega
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
  have hy_flat : y ∈ S.flatten := by rwa [List.flatten_splitBy]
  obtain ⟨b', hb', hyb'⟩ := List.mem_flatten.mp hy_flat
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb'
  rcases lt_trichotomy i j with hij | rfl | hji
  · exfalso
    have := hlt_all i j hij hj x hx y hyb'
    omega
  · exact hyb'
  · exfalso
    have := hlt_all j i hji hi y hyb' x hx
    omega

private lemma block_chain_down {n : ℕ} (hn : 1 ≤ n) {b : List ℕ} (hb : b ∈ blocks n)
    {u j : ℕ} (hmem : 2 ^ j * u ∈ b) : u ∈ b := by
  induction j with
  | zero => simpa using hmem
  | succ j ih =>
    apply ih
    have hL_pw : (n.divisors.sort (· ≤ ·)).Pairwise (· ≤ ·) :=
      Finset.pairwise_sort n.divisors (· ≤ ·)
    have hmem_div : 2 ^ (j + 1) * u ∈ n.divisors :=
      (Finset.mem_sort (· ≤ ·)).mp (mem_of_mem_splitBy hb hmem)
    have hdvd : 2 ^ (j + 1) * u ∣ n := (Nat.mem_divisors.mp hmem_div).1
    have hdvd_prev : 2 ^ j * u ∣ n := by
      refine dvd_trans ⟨2, ?_⟩ hdvd
      rw [pow_succ]; ring
    have hu_ne : 2 ^ j * u ≠ 0 := by
      intro h0
      rw [h0, zero_dvd_iff] at hdvd_prev
      omega
    have hprev_mem : 2 ^ j * u ∈ n.divisors.sort (· ≤ ·) :=
      (Finset.mem_sort (· ≤ ·)).mpr (Nat.mem_divisors.mpr ⟨hdvd_prev, by omega⟩)
    have h1 : 2 ^ j * u ≤ 2 * (2 ^ (j + 1) * u) := by
      rw [pow_succ]; ring_nf; omega
    have h2 : 2 ^ (j + 1) * u ≤ 2 * (2 ^ j * u) := by
      rw [pow_succ]; ring_nf; omega
    exact splitBy_closed hL_pw b hb (2 ^ (j + 1) * u) hmem (2 ^ j * u) hprev_mem h1 h2

private lemma block_chain_up {n : ℕ} (hn : 1 ≤ n) {b : List ℕ} (hb : b ∈ blocks n)
    {u : ℕ} (hu_mem : u ∈ b) (hu_odd : Odd u) {i : ℕ} (hi : i ≤ n.factorization 2) :
    2 ^ i * u ∈ b := by
  induction i with
  | zero => simpa using hu_mem
  | succ i ih =>
    have hprev : 2 ^ i * u ∈ b := ih (Nat.le_of_succ_le hi)
    have hL_pw : (n.divisors.sort (· ≤ ·)).Pairwise (· ≤ ·) :=
      Finset.pairwise_sort n.divisors (· ≤ ·)
    have hu_div : u ∈ n.divisors :=
      (Finset.mem_sort (· ≤ ·)).mp (mem_of_mem_splitBy hb hu_mem)
    have hu_dvd : u ∣ n := (Nat.mem_divisors.mp hu_div).1
    have hv_dvd : 2 ^ n.factorization 2 ∣ n := Nat.ordProj_dvd n 2
    have hcop : Nat.Coprime (2 ^ n.factorization 2) u := by
      refine Nat.Coprime.pow_left _ (Nat.prime_two.coprime_iff_not_dvd.mpr ?_)
      intro h
      exact Nat.not_even_iff_odd.mpr hu_odd (even_iff_two_dvd.mpr h)
    have hmul_dvd : 2 ^ n.factorization 2 * u ∣ n := hcop.mul_dvd_of_dvd_of_dvd hv_dvd hu_dvd
    have hi_dvd : 2 ^ (i + 1) * u ∣ n :=
      dvd_trans (mul_dvd_mul_right (Nat.pow_dvd_pow 2 hi) u) hmul_dvd
    have hi_mem : 2 ^ (i + 1) * u ∈ n.divisors.sort (· ≤ ·) :=
      (Finset.mem_sort (· ≤ ·)).mpr (Nat.mem_divisors.mpr ⟨hi_dvd, by omega⟩)
    have h1 : 2 ^ (i + 1) * u ≤ 2 * (2 ^ i * u) := by
      rw [pow_succ]; ring_nf; omega
    have h2 : 2 ^ i * u ≤ 2 * (2 ^ (i + 1) * u) := by
      rw [pow_succ]; ring_nf; omega
    exact splitBy_closed hL_pw b hb (2 ^ i * u) hprev (2 ^ (i + 1) * u) hi_mem h1 h2

private lemma two_pow_mul_odd_inj {i₁ i₂ u₁ u₂ : ℕ} (hu₁ : Odd u₁) (hu₂ : Odd u₂)
    (heq : 2 ^ i₁ * u₁ = 2 ^ i₂ * u₂) : u₁ = u₂ ∧ i₁ = i₂ := by
  have h1 : (2 ^ i₁ * u₁).factorization 2 = i₁ := by
    have hu₁_ne : u₁ ≠ 0 := by rintro rfl; exact absurd hu₁ (by decide)
    rw [Nat.factorization_mul (pow_ne_zero i₁ (by norm_num)) hu₁_ne, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    have h0 : u₁.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => Nat.not_even_iff_odd.mpr hu₁ (even_iff_two_dvd.mpr h))
    omega
  have h2 : (2 ^ i₂ * u₂).factorization 2 = i₂ := by
    have hu₂_ne : u₂ ≠ 0 := by rintro rfl; exact absurd hu₂ (by decide)
    rw [Nat.factorization_mul (pow_ne_zero i₂ (by norm_num)) hu₂_ne, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    have h0 : u₂.factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h => Nat.not_even_iff_odd.mpr hu₂ (even_iff_two_dvd.mpr h))
    omega
  have hi : i₁ = i₂ := by rw [← h1, ← h2, heq]
  subst hi
  have hu : u₁ = u₂ := mul_left_cancel₀ (pow_ne_zero i₁ (by norm_num)) heq
  exact ⟨hu, rfl⟩

private lemma length_eq_mul_countP {n : ℕ} (hn : 1 ≤ n) {b : List ℕ} (hb : b ∈ blocks n) :
    b.length = A001511 n * b.countP (fun d => decide (Odd d)) := by
  have hnodup : b.Nodup := nodup_of_mem_splitBy (Finset.sort_nodup n.divisors (· ≤ ·)) hb
  set B : Finset ℕ := b.toFinset
  set U : Finset ℕ := B.filter Odd
  set I : Finset ℕ := Finset.range (n.factorization 2 + 1)
  have hlen : b.length = B.card := (List.toFinset_card_of_nodup hnodup).symm
  have hcnt : b.countP (fun d => decide (Odd d)) = U.card := by
    rw [List.countP_eq_length_filter]
    have hfn : (b.filter (fun d => decide (Odd d))).Nodup := hnodup.filter _
    rw [← List.toFinset_card_of_nodup hfn]
    congr 1
    ext x
    simp [B, U]
  have hB_eq : B = (U ×ˢ I).image (fun p => 2 ^ p.2 * p.1) := by
    ext d
    simp only [Finset.mem_image, Finset.mem_product, B, U, I, List.mem_toFinset,
      Finset.mem_filter, Finset.mem_range, Prod.exists]
    constructor
    · intro hd
      have hd_div : d ∈ n.divisors := (Finset.mem_sort (· ≤ ·)).mp (mem_of_mem_splitBy hb hd)
      have hd_dvd : d ∣ n := (Nat.mem_divisors.mp hd_div).1
      have hd_ne : d ≠ 0 := by intro h0; rw [h0, zero_dvd_iff] at hd_dvd; omega
      set j := d.factorization 2
      set u := d / 2 ^ j
      have hdecomp : 2 ^ j * u = d := Nat.ordProj_mul_ordCompl_eq_self d 2
      have hu_odd : Odd u := by
        have hnot : ¬ 2 ∣ u := Nat.not_dvd_ordCompl Nat.prime_two hd_ne
        exact Nat.odd_iff.mpr (by omega)
      have hj_le : j ≤ n.factorization 2 :=
        (Nat.factorization_le_iff_dvd hd_ne (by omega)).mpr hd_dvd 2
      have hu_mem : u ∈ b := block_chain_down hn hb (by rwa [hdecomp])
      exact ⟨u, j, ⟨⟨hu_mem, hu_odd⟩, Nat.lt_succ_of_le hj_le⟩, hdecomp⟩
    · rintro ⟨u, i, ⟨⟨hu_mem, hu_odd⟩, hi_lt⟩, rfl⟩
      exact block_chain_up hn hb hu_mem hu_odd (Nat.lt_succ_iff.mp hi_lt)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => 2 ^ p.2 * p.1) (U ×ˢ I : Finset (ℕ × ℕ)) := by
    rintro ⟨u₁, i₁⟩ h1 ⟨u₂, i₂⟩ h2 heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, U, Finset.mem_filter] at h1 h2
    obtain ⟨rfl, rfl⟩ := two_pow_mul_odd_inj h1.1.2 h2.1.2 heq
    rfl
  rw [hlen, hcnt, hB_eq, Finset.card_image_of_injOn hinj, Finset.card_product,
    Finset.card_range, A001511, mul_comm]

theorem OMA.solution : type_of% @OMA.S_oeis_a384225.main := by
  intro n hn k hk
  have hb_mem : (blocks n)[k] ∈ blocks n := List.getElem_mem hk
  have hget : ((blocks n)[k]?).getD [] = (blocks n)[k] := by
    simp [List.getElem?_eq_getElem hk]
  rw [T, A384222, hget, length_eq_mul_countP hn hb_mem]
  have hpos : 0 < A001511 n := by rw [A001511]; omega
  rw [Nat.mul_div_right _ hpos]
