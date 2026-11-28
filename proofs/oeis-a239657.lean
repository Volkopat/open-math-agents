import OMAStatements.S_oeis_a239657

-- Problem: A239657: odd divisors m of n with a divisor d < m < 2d (Pol's conjecture, Nov 2025).
-- Upstream: formal-conjectures statements/oeis-a239657.lean:0 (declaration OMA.S_oeis_a239657.main)
-- Credit: @nerotulip90 (the owner of the agent is credited as the solver)
-- Proof: partitions of n into consecutive parts (a, k) satisfy k(2a+k-1) = 2n and correspond
-- bijectively to odd divisors (take the odd factor). The 2-dense blocks of divisors have distinct odd
-- heads, and an odd divisor is a head iff no divisor d has d < m < 2d; so A239657(n) counts the odd
-- divisors that are not heads = #odd divisors - #blocks.

namespace OMA.W2_a239657

open List

abbrev r : ℕ → ℕ → Bool := fun d e => decide (e ≤ 2 * d)

lemma le_getLast_of_pw {l : List ℕ} (hl : l.Pairwise (· < ·)) (hne : l ≠ []) {x : ℕ}
    (hx : x ∈ l) : x ≤ l.getLast hne := by
  have e := List.dropLast_append_getLast hne
  rw [← e] at hl hx
  rw [List.pairwise_append] at hl
  rcases List.mem_append.mp hx with h | h
  · exact (hl.2.2 x h _ (by simp)).le
  · simp at h; omega

lemma head_le_of_pw {l : List ℕ} (hl : l.Pairwise (· < ·)) (hne : l ≠ []) {x : ℕ}
    (hx : x ∈ l) : l.head hne ≤ x := by
  obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.head_cons]
  rcases List.mem_cons.mp hx with h | h
  · omega
  · exact (List.rel_of_pairwise_cons hl h).le

lemma pred_exists : ∀ {l : List ℕ}, l.Pairwise (· < ·) → l.IsChain (fun x y => r x y = true) →
    ∀ (hne : l ≠ []) {a : ℕ}, a ∈ l → a ≠ l.head hne → ∃ b ∈ l, b < a ∧ a ≤ 2 * b
  | [], _, _, hne, _, _, _ => absurd rfl hne
  | [x], _, _, _, a, ha, hah => by simp at ha; simp [ha] at hah
  | x :: y :: t, hp, hc, _, a, ha, hah => by
      simp only [List.head_cons] at hah
      rw [List.isChain_cons_cons] at hc
      have hxy : x < y := List.rel_of_pairwise_cons hp (by simp)
      by_cases hay : a = y
      · subst hay; exact ⟨x, by simp, hxy, by simpa using hc.1⟩
      · have ha' : a ∈ y :: t := by
          rcases List.mem_cons.mp ha with h | h
          · exact absurd h hah
          · exact h
        obtain ⟨b, hb, h1, h2⟩ :=
          pred_exists (List.Pairwise.of_cons hp) hc.2 (List.cons_ne_nil _ _) ha' (by simpa using hay)
        exact ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩


section blocks
variable {l : List ℕ} (hl : l.Pairwise (· < ·)) {P T : List (List ℕ)} {K : List ℕ}
  (hb : l.splitBy r = P ++ K :: T)
include hl hb

lemma l_eq : l = P.flatten ++ K ++ T.flatten := by
  have := List.flatten_splitBy r l
  rw [hb] at this; simp [← this]

lemma K_ne : K ≠ [] := List.ne_nil_of_mem_splitBy (r := r) (l := l) (by rw [hb]; simp)

lemma K_pw : K.Pairwise (· < ·) := by
  have h := hl; rw [l_eq hl hb, List.pairwise_append, List.pairwise_append] at h; exact h.1.2.1

lemma K_chain : K.IsChain (fun x y => r x y = true) :=
  List.isChain_of_mem_splitBy (l := l) (by rw [hb]; simp)

lemma lt_K {x y : ℕ} (hx : x ∈ P.flatten) (hy : y ∈ K) : x < y := by
  have h := hl; rw [l_eq hl hb, List.pairwise_append, List.pairwise_append] at h
  exact h.1.2.2 x hx y hy

lemma K_lt {x y : ℕ} (hx : x ∈ K) (hy : y ∈ T.flatten) : x < y := by
  have h := hl; rw [l_eq hl hb, List.pairwise_append] at h
  exact h.2.2 x (by simp [hx]) y hy

lemma mem_K_of_between {x : ℕ} (hx : x ∈ l) (h1 : K.head (K_ne hl hb) ≤ x)
    (h2 : x ≤ K.getLast (K_ne hl hb)) : x ∈ K := by
  rw [l_eq hl hb] at hx
  rcases List.mem_append.mp hx with h | h
  · rcases List.mem_append.mp h with h | h
    · have := lt_K hl hb h (List.head_mem (K_ne hl hb)); omega
    · exact h
  · have := K_lt hl hb (List.getLast_mem (K_ne hl hb)) h; omega

lemma gap_before (hP : P ≠ []) {x : ℕ} (hx : x ∈ l) (hlt : x < K.head (K_ne hl hb)) :
    2 * x < K.head (K_ne hl hb) := by
  have hxP : x ∈ P.flatten := by
    rw [l_eq hl hb] at hx
    rcases List.mem_append.mp hx with h | h
    · rcases List.mem_append.mp h with h | h
      · exact h
      · have := head_le_of_pw (K_pw hl hb) (K_ne hl hb) h; omega
    · have := K_lt hl hb (List.head_mem (K_ne hl hb)) h; omega
  set Q := P.getLast hP with hQ
  have hPe : P = P.dropLast ++ [Q] := (List.dropLast_append_getLast hP).symm
  have hQne : Q ≠ [] := List.ne_nil_of_mem_splitBy (r := r) (l := l)
    (by rw [hb]; exact List.mem_append_left _ (List.getLast_mem hP))
  have hch := List.isChain_getLast_head_splitBy r l
  rw [hb, hPe, List.append_assoc, List.singleton_append, List.isChain_append] at hch
  have hch2 := hch.2.1
  rw [List.isChain_cons_cons] at hch2
  obtain ⟨_, _, hrel⟩ := hch2.1
  simp only [r, decide_eq_false_iff_not, not_le] at hrel
  have hpw : (P.dropLast.flatten ++ Q).Pairwise (· < ·) := by
    have h := hl; rw [l_eq hl hb, List.pairwise_append, List.pairwise_append] at h
    have := h.1.1; rw [hPe] at this; simpa using this
  have hxle : x ≤ Q.getLast hQne := by
    have hxP' : x ∈ P.dropLast.flatten ++ Q := by rw [hPe] at hxP; simpa using hxP
    rcases List.mem_append.mp hxP' with h | h
    · rw [List.pairwise_append] at hpw
      exact (hpw.2.2 x h _ (List.getLast_mem hQne)).le
    · exact le_getLast_of_pw (List.pairwise_append.mp hpw).2.1 hQne h
  omega

lemma gap_after (hT : T ≠ []) {x : ℕ} (hx : x ∈ l) (hlt : K.getLast (K_ne hl hb) < x) :
    2 * K.getLast (K_ne hl hb) < x := by
  have hxT : x ∈ T.flatten := by
    rw [l_eq hl hb] at hx
    rcases List.mem_append.mp hx with h | h
    · rcases List.mem_append.mp h with h | h
      · have := lt_K hl hb h (List.getLast_mem (K_ne hl hb)); omega
      · have := le_getLast_of_pw (K_pw hl hb) (K_ne hl hb) h; omega
    · exact h
  obtain ⟨U, T', rfl⟩ := List.exists_cons_of_ne_nil hT
  have hUne : U ≠ [] := List.ne_nil_of_mem_splitBy (r := r) (l := l) (by rw [hb]; simp)
  have hch := List.isChain_getLast_head_splitBy r l
  rw [hb, List.isChain_append] at hch
  have hch2 := hch.2.1
  rw [List.isChain_cons_cons] at hch2
  obtain ⟨_, _, hrel⟩ := hch2.1
  simp only [r, decide_eq_false_iff_not, not_le] at hrel
  have hpw : (U ++ T'.flatten).Pairwise (· < ·) := by
    have h := hl; rw [l_eq hl hb, List.pairwise_append] at h
    simpa using h.2.1
  have hxge : U.head hUne ≤ x := by
    have hxT' : x ∈ U ++ T'.flatten := by simpa using hxT
    rcases List.mem_append.mp hxT' with h | h
    · exact head_le_of_pw (List.pairwise_append.mp hpw).1 hUne h
    · rw [List.pairwise_append] at hpw
      exact (hpw.2.2 _ (List.head_mem hUne) x h).le
  omega

end blocks



open OMA.S_oeis_a239657

lemma two_sum (a k : ℕ) (hk : 1 ≤ k) :
    2 * ∑ i ∈ Finset.range k, (a + i) = k * (2 * a + k - 1) := by
  rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_comm 2 (∑ i ∈ Finset.range k, i), Finset.sum_range_id_mul_two]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [show 2 * a + (j + 1) - 1 = 2 * a + j by omega]
  ring

/-- Partitions into consecutive parts are counted by the odd divisors. -/
lemma card_consecParts (n : ℕ) (hn : 1 ≤ n) :
    (consecParts n).card = (n.divisors.filter Odd).card := by
  classical
  let f : ℕ × ℕ → ℕ := fun p => if Odd p.2 then p.2 else 2 * p.1 + p.2 - 1
  let g : ℕ → ℕ × ℕ := fun o =>
    if o < 2 * (n / o) then ((2 * (n / o) - o + 1) / 2, o) else ((o - 2 * (n / o) + 1) / 2, 2 * (n / o))
  have memC : ∀ a k, (a, k) ∈ consecParts n ↔ 1 ≤ a ∧ a ≤ n ∧ 1 ≤ k ∧ k ≤ n ∧
      k * (2 * a + k - 1) = 2 * n := by
    intro a k
    simp only [consecParts, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
      exact ⟨h1, h2, h3, h4, by rw [← two_sum a k h3, h5]⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨⟨⟨h1, h2⟩, h3, h4⟩, ?_⟩
      have := two_sum a k h3; omega
  refine Finset.card_bij' (fun p _ => f p) (fun o _ => g o) ?_ ?_ ?_ ?_
  · rintro ⟨a, k⟩ hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := (memC a k).mp hp
    simp only [Finset.mem_filter, Nat.mem_divisors, f]
    refine ⟨⟨?_, by omega⟩, ?_⟩
    · split_ifs with hk
      · have : k ∣ 2 * n := ⟨_, h5.symm⟩
        exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hk |>.symm |> fun h => by
          exact Nat.Coprime.symm (Nat.coprime_comm.mp (Nat.Coprime.symm h))) this)
      · have hj : Odd (2 * a + k - 1) := by
          rcases Nat.not_odd_iff_even.mp hk with ⟨t, ht⟩
          exact ⟨a + t - 1, by omega⟩
        have : (2 * a + k - 1) ∣ 2 * n := ⟨k, by rw [← h5]; ring⟩
        exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hj) this
    · split_ifs with hk
      · exact hk
      · rcases Nat.not_odd_iff_even.mp hk with ⟨t, ht⟩
        exact ⟨a + t - 1, by omega⟩
  · intro o ho
    simp only [Finset.mem_filter, Nat.mem_divisors] at ho
    obtain ⟨⟨⟨t, ht⟩, -⟩, hoo⟩ := ho
    have hopos : 0 < o := hoo.pos
    have hdiv : n / o = t := by rw [ht]; exact Nat.mul_div_cancel_left t hopos
    have htpos : 0 < t := by rcases Nat.eq_zero_or_pos t with h | h <;> [simp [h] at ht; exact h] <;> omega
    obtain ⟨u, hu⟩ := hoo
    simp only [g, hdiv]
    split_ifs with hlt
    · rw [memC]
      have e2 : 2 * ((2 * t - o + 1) / 2) = 2 * t - o + 1 := by omega
      refine ⟨by omega, ?_, by omega, by nlinarith, ?_⟩
      · have : t ≤ o * t := Nat.le_mul_of_pos_left t hopos
        omega
      · rw [e2, show 2 * t - o + 1 + o - 1 = 2 * t by omega, ht]; ring
    · rw [memC]
      have e2 : 2 * ((o - 2 * t + 1) / 2) = o - 2 * t + 1 := by omega
      have hto : t ≤ n := by rw [ht]; nlinarith
      refine ⟨by omega, ?_, by omega, by nlinarith, ?_⟩
      · have : o ≤ n := by rw [ht]; nlinarith
        omega
      · rw [e2, show o - 2 * t + 1 + 2 * t - 1 = o by omega, ht]; ring
  · rintro ⟨a, k⟩ hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := (memC a k).mp hp
    simp only [f]
    split_ifs with hk
    · -- o = k, n / k = (2a+k-1)/2 ... use 2n = k * j
      have hj : 2 * a + k - 1 = 2 * (n / k) := by
        obtain ⟨u, hu⟩ := hk
        have hkn : k ∣ n := Nat.Coprime.dvd_of_dvd_mul_left
          (Nat.coprime_two_right.mpr ⟨u, hu⟩) ⟨_, h5.symm⟩
        obtain ⟨t, ht⟩ := hkn
        rw [ht, Nat.mul_div_cancel_left t (by omega)]
        have : k * (2 * a + k - 1) = k * (2 * t) := by rw [h5, ht]; ring
        exact Nat.eq_of_mul_eq_mul_left (by omega) this
      simp only [g]
      rw [if_pos (by omega)]
      ext <;> simp <;> omega
    · rcases Nat.not_odd_iff_even.mp hk with ⟨t, ht⟩
      set j := 2 * a + k - 1 with hjdef
      have hjpos : 0 < j := by omega
      have hq : n / j = t := by
        have : n = j * t := by
          have : 2 * n = 2 * (j * t) := by rw [← h5, ht]; ring
          omega
        rw [this]; exact Nat.mul_div_cancel_left t hjpos
      simp only [g, hq]
      rw [if_neg (by omega)]
      ext <;> simp <;> omega
  · intro o ho
    simp only [Finset.mem_filter, Nat.mem_divisors] at ho
    obtain ⟨⟨⟨t, ht⟩, -⟩, hoo⟩ := ho
    have hopos : 0 < o := hoo.pos
    have hdiv : n / o = t := by rw [ht]; exact Nat.mul_div_cancel_left t hopos
    obtain ⟨u, hu⟩ := hoo
    by_cases hlt : o < 2 * t
    · have : Odd o := ⟨u, hu⟩
      simp [g, hdiv, f, hlt, this]
    · have h2t : ¬ Odd (2 * t) := Nat.not_odd_iff_even.mpr (even_two_mul t)
      simp only [g, hdiv, f, hlt, if_false, h2t]
      omega

theorem key (n : ℕ) (hn : 1 ≤ n) : A239657 n = (consecParts n).card - (blocks n).length := by
  rw [card_consecParts n hn]
  set S := n.divisors.sort (· ≤ ·) with hSdef
  have hS : S.Pairwise (· < ·) := by
    have h1 := Finset.pairwise_sort n.divisors (· ≤ ·)
    have h2 := Finset.sort_nodup n.divisors (· ≤ ·)
    exact (h1.and h2).imp fun h => lt_of_le_of_ne h.1 h.2
  have memS : ∀ x, x ∈ S ↔ x ∣ n := fun x => by
    rw [Finset.mem_sort, Nat.mem_divisors]; exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
  have hSne : S ≠ [] := fun h => by
    have := (memS 1).mpr (one_dvd n); rw [h] at this; simp at this
  have hheadS : S.head hSne = 1 := by
    have h1 := head_le_of_pw hS hSne ((memS 1).mpr (one_dvd n))
    have h2 : 0 < S.head hSne := Nat.pos_of_dvd_of_pos ((memS _).mp (List.head_mem hSne)) (by omega)
    omega
  set H := (S.splitBy r).map (fun K => K.headD 0) with hH
  have hBL : (blocks n).length = H.length := by simp [blocks, hH]; rfl
  have head_facts : ∀ K ∈ S.splitBy r, ∃ hK : K ≠ [], (K.headD 0 = K.head hK) ∧
      (∀ d, d ∣ n → ¬ (d < K.head hK ∧ K.head hK < 2 * d)) ∧ Odd (K.head hK) := by
    intro K hK
    obtain ⟨P, T, hb⟩ := List.append_of_mem hK
    have hKne := K_ne hS hb
    refine ⟨hKne, by cases K with | nil => exact absurd rfl hKne | cons _ _ => rfl, ?_⟩
    rcases P.eq_nil_or_concat with hP | ⟨P', Q, hP⟩
    · subst hP
      have h1 : K.head hKne = 1 := by
        have := List.head_head_splitBy r hSne
        simp only [hb, List.nil_append, List.head_cons] at this
        rw [this, hheadS]
      rw [h1]; exact ⟨fun d _ h => by omega, odd_one⟩
    · have hPne : P ≠ [] := by rw [hP]; simp
      have hdS : K.head hKne ∈ S := by
        rw [l_eq hS hb]; exact List.mem_append_left _ (List.mem_append_right _ (List.head_mem hKne))
      refine ⟨fun d hd h => ?_, ?_⟩
      · have := gap_before hS hb hPne ((memS d).mpr hd) h.1; omega
      · rcases Nat.even_or_odd (K.head hKne) with ⟨t, ht⟩ | ho
        · have htd : t ∣ n := Dvd.dvd.trans ⟨2, by omega⟩ ((memS _).mp hdS)
          have hpos : 0 < K.head hKne := Nat.pos_of_dvd_of_pos ((memS _).mp hdS) (by omega)
          have := gap_before hS hb hPne ((memS t).mpr htd) (by omega)
          omega
        · exact ho
  have hHnd : H.Nodup := by
    have hpw := hS
    rw [← List.flatten_splitBy r S, List.pairwise_flatten] at hpw
    have : H.Pairwise (· < ·) := by
      rw [hH, List.pairwise_map]
      refine hpw.2.imp_of_mem fun {K1 K2} h1 h2 h => ?_
      obtain ⟨hK1, e1, -⟩ := head_facts K1 h1
      obtain ⟨hK2, e2, -⟩ := head_facts K2 h2
      rw [e1, e2]; exact h _ (List.head_mem hK1) _ (List.head_mem hK2)
    exact this.imp ne_of_lt
  set O := n.divisors.filter Odd with hO
  have hHO : H.toFinset ⊆ O := by
    intro x hx
    simp only [List.mem_toFinset, hH, List.mem_map] at hx
    obtain ⟨K, hK, rfl⟩ := hx
    obtain ⟨hKne, e1, -, hodd⟩ := head_facts K hK
    rw [e1, hO, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, by omega⟩, hodd⟩
    rw [← memS, ← List.flatten_splitBy r S]
    exact List.mem_flatten.mpr ⟨K, hK, List.head_mem hKne⟩
  have hOH : ∀ o ∈ O, (∀ d, d ∣ n → ¬ (d < o ∧ o < 2 * d)) → o ∈ H.toFinset := by
    intro o ho hno
    rw [hO, Finset.mem_filter, Nat.mem_divisors] at ho
    have hoS : o ∈ S := (memS o).mpr ho.1.1
    rw [← List.flatten_splitBy r S] at hoS
    obtain ⟨K, hK, hoK⟩ := List.mem_flatten.mp hoS
    obtain ⟨P, T, hb⟩ := List.append_of_mem hK
    obtain ⟨hKne, e1, -, -⟩ := head_facts K hK
    by_cases hoh : o = K.head hKne
    · simp only [List.mem_toFinset, hH, List.mem_map]
      exact ⟨K, hK, by rw [e1, hoh]⟩
    · obtain ⟨b, hbK, hbo, hob⟩ := pred_exists (K_pw hS hb) (K_chain hS hb) hKne hoK hoh
      have hbS : b ∈ S := by rw [l_eq hS hb]; simp [hbK]
      have hne : o ≠ 2 * b := fun h => by
        have := ho.2; rw [h] at this; exact (Nat.not_odd_iff_even.mpr (even_two_mul b)) this
      exact absurd ⟨hbo, by omega⟩ (hno b ((memS b).mp hbS))
  have hHno : ∀ o ∈ H.toFinset, ∀ d, d ∣ n → ¬ (d < o ∧ o < 2 * d) := by
    intro o ho
    simp only [List.mem_toFinset, hH, List.mem_map] at ho
    obtain ⟨K, hK, rfl⟩ := ho
    obtain ⟨hKne, e1, hgap, -⟩ := head_facts K hK
    rw [e1]; exact hgap
  have hcardH : H.toFinset.card = H.length := List.toFinset_card_of_nodup hHnd
  have hset : n.divisors.filter (fun m => Odd m ∧ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d) =
      O \ H.toFinset := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_sdiff, hO, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, hodd, d, hdd, h1, h2⟩
      refine ⟨⟨hd, hodd⟩, fun hH' => hHno o hH' d hdd.1 ⟨h1, h2⟩⟩
    · rintro ⟨⟨hd, hodd⟩, hnH⟩
      refine ⟨hd, hodd, ?_⟩
      by_contra hno
      push Not at hno
      exact hnH (hOH o (by rw [hO, Finset.mem_filter, Nat.mem_divisors]; exact ⟨hd, hodd⟩)
        fun d hdn h => by
          have := hno d ⟨hdn, by omega⟩ h.1; omega)
  rw [A239657, hset, Finset.card_sdiff_of_subset hHO, hcardH, hBL]

end OMA.W2_a239657

open OMA.W2_a239657 in
theorem OMA.solution : type_of% @OMA.S_oeis_a239657.main := fun n hn => key n hn
