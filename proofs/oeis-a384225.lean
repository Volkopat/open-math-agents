import OMAStatements.S_oeis_a384225

-- Problem: A384225 (Conjecture 2: T(n,k) = A384222(n,k) / A001511(n))
-- Upstream: formal-conjectures statements/oeis-a384225.lean:0 (declaration OMA.S_oeis_a384225.main)
-- Credit: @SSmurf

namespace OMA.S_oeis_a384225

lemma le_getLast_of_pairwise_lt (l : List ℕ) (h : l.Pairwise (· < ·)) (hne : l ≠ [])
    (a : ℕ) (ha : a ∈ l) : a ≤ l.getLast hne := by
  have hl := List.dropLast_append_getLast hne
  have h' : (l.dropLast ++ [l.getLast hne]).Pairwise (· < ·) := by rw [hl]; exact h
  have ha' : a ∈ l.dropLast ++ [l.getLast hne] := by rw [hl]; exact ha
  rw [List.pairwise_append] at h'
  rcases List.mem_append.mp ha' with h1 | h1
  · exact le_of_lt (h'.2.2 a h1 _ (by simp))
  · simp at h1; omega

lemma head_le_of_pairwise_lt (l : List ℕ) (h : l.Pairwise (· < ·)) (hne : l ≠ [])
    (a : ℕ) (ha : a ∈ l) : l.head hne ≤ a := by
  cases l with
  | nil => exact absurd rfl hne
  | cons b t =>
    simp only [List.head_cons]
    rcases List.mem_cons.mp ha with h1 | h1
    · exact le_of_eq h1.symm
    · exact le_of_lt ((List.pairwise_cons.mp h).1 a h1)

lemma same_block (L : List ℕ) (hL : L.Pairwise (· < ·)) (x : ℕ) (hx : x ∈ L)
    (h2 : 2 * x ∈ L) (hx0 : 0 < x)
    (B : List ℕ) (hB : B ∈ L.splitBy (fun d e => decide (e ≤ 2 * d))) :
    x ∈ B ↔ 2 * x ∈ B := by
  have hch := List.isChain_getLast_head_splitBy (fun d e => decide (e ≤ 2 * d)) L
  have hflat := List.flatten_splitBy (fun d e => decide (e ≤ 2 * d)) L
  generalize L.splitBy (fun d e => decide (e ≤ 2 * d)) = P at *
  have hpw : P.flatten.Pairwise (· < ·) := by rw [hflat]; exact hL
  rw [List.pairwise_flatten] at hpw
  obtain ⟨hin, hbt⟩ := hpw
  rw [List.pairwise_iff_getElem] at hbt
  rw [List.isChain_iff_getElem] at hch
  have huniq : ∀ (a : ℕ) (i j : ℕ) (hi : i < P.length) (hj : j < P.length),
      a ∈ P[i] → a ∈ P[j] → i = j := by
    intro a i j hi hj hai haj
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd (hbt i j hi hj h a hai a haj) (lt_irrefl _)
    · exact h
    · exact absurd (hbt j i hj hi h a haj a hai) (lt_irrefl _)
  have hxL : x ∈ P.flatten := by rw [hflat]; exact hx
  have h2L : 2 * x ∈ P.flatten := by rw [hflat]; exact h2
  obtain ⟨Bx, hBx, hxBx⟩ := List.mem_flatten.mp hxL
  obtain ⟨By, hBy, hyBy⟩ := List.mem_flatten.mp h2L
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hBx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hBy
  have hij : i = j := by
    rcases Nat.lt_trichotomy i j with h | h | h
    · exfalso
      have hi1 : i + 1 < P.length := by omega
      obtain ⟨ha, hb, hr⟩ := hch i hi1
      have hr' : 2 * P[i].getLast ha < P[i + 1].head hb := by simpa using hr
      have h1 := le_getLast_of_pairwise_lt P[i] (hin _ (List.getElem_mem hi)) ha x hxBx
      have h3 : P[i + 1].head hb ≤ 2 * x := by
        rcases Nat.lt_or_ge (i + 1) j with h4 | h4
        · exact le_of_lt (hbt (i + 1) j hi1 hj h4 _ (List.head_mem hb) _ hyBy)
        · have h5 : i + 1 = j := by omega
          subst h5
          exact head_le_of_pairwise_lt _ (hin _ (List.getElem_mem hi1)) hb _ hyBy
      omega
    · exact h
    · exfalso
      have := hbt j i hj hi h _ hyBy _ hxBx
      omega
  subst hij
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hB
  constructor
  · intro h
    have := huniq x m i hm hi h hxBx
    subst this; exact hyBy
  · intro h
    have := huniq (2 * x) m i hm hi h hyBy
    subst this; exact hxBx

lemma block_props (L : List ℕ) (hL : L.Pairwise (· < ·))
    (B : List ℕ) (hB : B ∈ L.splitBy (fun d e => decide (e ≤ 2 * d))) :
    B.Pairwise (· < ·) ∧ ∀ a ∈ B, a ∈ L := by
  have hflat := List.flatten_splitBy (fun d e => decide (e ≤ 2 * d)) L
  have hpw : (L.splitBy (fun d e => decide (e ≤ 2 * d))).flatten.Pairwise (· < ·) := by
    rw [hflat]; exact hL
  rw [List.pairwise_flatten] at hpw
  refine ⟨hpw.1 B hB, fun a ha => ?_⟩
  rw [← hflat]
  exact List.mem_flatten.mpr ⟨B, hB, ha⟩

lemma odd_mul_pow_inj (o1 o2 i1 i2 : ℕ) (h1 : Odd o1) (h2 : Odd o2)
    (h : o1 * 2 ^ i1 = o2 * 2 ^ i2) : o1 = o2 ∧ i1 = i2 := by
  have key : ∀ (a b i d : ℕ), Odd a → a * 2 ^ i = b * 2 ^ (i + d + 1) → False := by
    intro a b i d ha hab
    have : a * 2 ^ i = (b * 2 ^ d * 2) * 2 ^ i := by rw [hab]; ring
    have h3 := Nat.eq_of_mul_eq_mul_right (by positivity) this
    rcases ha with ⟨t, ht⟩
    omega
  rcases Nat.lt_trichotomy i1 i2 with hlt | heq | hgt
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, i2 = i1 + d + 1 := ⟨i2 - i1 - 1, by omega⟩
    exact key o1 o2 i1 d h1 h
  · subst heq
    exact ⟨Nat.eq_of_mul_eq_mul_right (by positivity) h, rfl⟩
  · exfalso
    obtain ⟨d, rfl⟩ : ∃ d, i1 = i2 + d + 1 := ⟨i1 - i2 - 1, by omega⟩
    exact key o2 o1 i2 d h2 h.symm

end OMA.S_oeis_a384225

open OMA.S_oeis_a384225 in
theorem OMA.solution : type_of% @OMA.S_oeis_a384225.main := by
  intro n hn k hk
  have hn0 : n ≠ 0 := by omega
  unfold T A384222 A001511
  have hBk : (blocks n)[k]? = some (blocks n)[k] := List.getElem?_eq_getElem hk
  rw [hBk]
  simp only [Option.getD_some]
  have hBmem : (blocks n)[k] ∈ blocks n := List.getElem_mem hk
  generalize (blocks n)[k] = B at hBmem ⊢
  unfold blocks at hBmem
  set L := n.divisors.sort (· ≤ ·) with hLdef
  have hL : L.Pairwise (· < ·) := by
    have h1 : L.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
    have h2 : L.Nodup := Finset.sort_nodup _ _
    exact (h1.and h2).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hLmem : ∀ d, d ∈ L ↔ d ∣ n := by
    intro d
    rw [hLdef, Finset.mem_sort, Nat.mem_divisors]
    exact ⟨fun h => h.1, fun h => ⟨h, hn0⟩⟩
  obtain ⟨hBpw, hBL⟩ := block_props L hL B hBmem
  have hBnd : B.Nodup := hBpw.imp (fun h => ne_of_lt h)
  set e := n.factorization 2 with he
  suffices h : B.length = (e + 1) * B.countP (fun d => decide (Odd d)) by
    rw [h, Nat.mul_div_cancel_left _ (Nat.succ_pos _)]
  -- upward closure
  have hup : ∀ o, o ∈ B → Odd o → ∀ i, i ≤ e → o * 2 ^ i ∈ B := by
    intro o ho hodd i
    induction i with
    | zero => intro _; simpa using ho
    | succ i ih =>
      intro hi
      have hx := ih (by omega)
      have hdvd : o * 2 ^ (i + 1) ∣ n := by
        have h1 : o ∣ n := (hLmem o).mp (hBL o ho)
        have h2 : 2 ^ (i + 1) ∣ n := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0).mpr hi
        have hc : Nat.Coprime o (2 ^ (i + 1)) :=
          Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)
        exact hc.mul_dvd_of_dvd_of_dvd h1 h2
      have hx0 : 0 < o * 2 ^ i := by
        have : o * 2 ^ i ∣ n := (hLmem _).mp (hBL _ hx)
        exact Nat.pos_of_dvd_of_pos this (by omega)
      have h2x : 2 * (o * 2 ^ i) ∈ L := by
        rw [hLmem]
        have : 2 * (o * 2 ^ i) = o * 2 ^ (i + 1) := by ring
        rw [this]; exact hdvd
      have := (same_block L hL (o * 2 ^ i) (hBL _ hx) h2x hx0 B hBmem).mp hx
      have e2 : o * 2 ^ (i + 1) = 2 * (o * 2 ^ i) := by ring
      rw [e2]; exact this
  -- downward closure
  have hdown : ∀ i o, o * 2 ^ i ∈ B → o ∈ B := by
    intro i
    induction i with
    | zero => intro o ho; simpa using ho
    | succ i ih =>
      intro o ho
      apply ih
      have e2 : o * 2 ^ (i + 1) = 2 * (o * 2 ^ i) := by ring
      rw [e2] at ho
      have h2L := hBL _ ho
      have hdvd : 2 * (o * 2 ^ i) ∣ n := (hLmem _).mp h2L
      have hxd : o * 2 ^ i ∣ n := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hdvd
      have hx0 : 0 < o * 2 ^ i := Nat.pos_of_dvd_of_pos hxd (by omega)
      exact (same_block L hL (o * 2 ^ i) ((hLmem _).mpr hxd) h2L hx0 B hBmem).mpr ho
  -- counting
  have hlen : B.length = B.toFinset.card := (List.toFinset_card_of_nodup hBnd).symm
  have hcnt : B.countP (fun d => decide (Odd d)) = (B.toFinset.filter (fun d => Odd d)).card := by
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hBnd.filter _),
      List.toFinset_filter]
    simp
  have himg : B.toFinset = ((B.toFinset.filter (fun d => Odd d)) ×ˢ Finset.range (e + 1)).image
      (fun p : ℕ × ℕ => p.1 * 2 ^ p.2) := by
    ext d
    simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_product, Finset.mem_filter,
      Finset.mem_range, Prod.exists]
    constructor
    · intro hd
      have hdn : d ∣ n := (hLmem d).mp (hBL d hd)
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hn0 (Nat.eq_zero_of_zero_dvd hdn)
      obtain ⟨i, o, hodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hd0
      refine ⟨o, i, ⟨⟨?_, hodd⟩, ?_⟩, by ring⟩
      · apply hdown i
        rw [mul_comm]; exact hd
      · have : 2 ^ i ∣ n := Dvd.dvd.trans (Dvd.intro _ rfl) hdn
        have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0).mp this
        omega
    · rintro ⟨o, i, ⟨⟨ho, hodd⟩, hi⟩, rfl⟩
      exact hup o ho hodd i (by omega)
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * 2 ^ p.2)
      (((B.toFinset.filter (fun d => Odd d)) ×ˢ Finset.range (e + 1) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    rintro ⟨o1, i1⟩ h1 ⟨o2, i2⟩ h2 h
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter] at h1 h2
    obtain ⟨rfl, rfl⟩ := odd_mul_pow_inj o1 o2 i1 i2 h1.1.2 h2.1.2 h
    rfl
  rw [hlen, hcnt, himg, Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
    ← himg]
  ring
