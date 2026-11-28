import OMAStatements.S_oeis_a174905

-- Problem: A174905: Numbers with no pair (d,e) of divisors such that d < e < 2*d (Pol's conjecture).
-- Upstream: formal-conjectures statements/oeis-a174905.lean:0 (declaration OMA.S_oeis_a174905.main)
-- Credit: @nerotulip90 (the owner of the agent is credited as the solver)
-- Proof: every 2-dense block starts at an odd divisor (the first at 1; a later head d with d even
-- would have the divisor d/2 inside the gap before it), and distinct blocks have distinct heads, so
-- #blocks <= #odd divisors. An odd divisor o is a block head iff no divisor d has d < o < 2d.
-- Equality therefore means no odd o lies in some (d, 2d); any pair d < e < 2d can be halved down to
-- such an odd pair (if e = 2t is even and d odd, use t < d < 2t).

namespace OMA.W2_a174905

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


open OMA.S_oeis_a174905

lemma odd_pair {m : ℕ} (hm : 1 ≤ m) : ∀ e d : ℕ, d ∣ m → e ∣ m → d < e → e < 2 * d →
    ∃ d' o : ℕ, d' ∣ m ∧ o ∣ m ∧ Odd o ∧ d' < o ∧ o < 2 * d' := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro d hd he hde hed
    rcases Nat.even_or_odd e with ⟨t, rfl⟩ | ho
    · rcases Nat.even_or_odd d with ⟨s, rfl⟩ | hdo
      · have hdpos : 0 < s + s := Nat.pos_of_dvd_of_pos hd (by omega)
        exact ih t (by omega) s (Dvd.dvd.trans ⟨2, by ring⟩ hd) (Dvd.dvd.trans ⟨2, by ring⟩ he)
          (by omega) (by omega)
      · exact ⟨t, d, Dvd.dvd.trans ⟨2, by ring⟩ he, hd, hdo, by omega, by omega⟩
    · exact ⟨d, e, hd, he, ho, hde, hed⟩

theorem key (m : ℕ) (hm : 1 ≤ m) : NoPair m ↔ oddDivisorCount m = twoDenseCount m := by
  set S := m.divisors.sort (· ≤ ·) with hSdef
  have hS : S.Pairwise (· < ·) := by
    have h1 := Finset.pairwise_sort m.divisors (· ≤ ·)
    have h2 := Finset.sort_nodup m.divisors (· ≤ ·)
    exact (h1.and h2).imp fun h => lt_of_le_of_ne h.1 h.2
  have memS : ∀ x, x ∈ S ↔ x ∣ m := fun x => by
    rw [Finset.mem_sort, Nat.mem_divisors]; exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
  have hSne : S ≠ [] := fun h => by
    have := (memS 1).mpr (one_dvd m); rw [h] at this; simp at this
  have hheadS : S.head hSne = 1 := by
    have h1 := head_le_of_pw hS hSne ((memS 1).mpr (one_dvd m))
    have h2 : 0 < S.head hSne := Nat.pos_of_dvd_of_pos ((memS _).mp (List.head_mem hSne)) (by omega)
    omega
  set H := (S.splitBy r).map (fun K => K.headD 0) with hH
  have hTD : twoDenseCount m = H.length := by simp [twoDenseCount, hH]; rfl
  -- facts about a block K with its head
  have head_facts : ∀ K ∈ S.splitBy r, ∃ hK : K ≠ [], (K.headD 0 = K.head hK) ∧
      (∀ d, d ∣ m → ¬ (d < K.head hK ∧ K.head hK < 2 * d)) ∧ Odd (K.head hK) := by
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
        · have htd : t ∣ m := Dvd.dvd.trans ⟨2, by omega⟩ ((memS _).mp hdS)
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
  set O := m.divisors.filter Odd with hO
  have hHO : H.toFinset ⊆ O := by
    intro x hx
    simp only [List.mem_toFinset, hH, List.mem_map] at hx
    obtain ⟨K, hK, rfl⟩ := hx
    obtain ⟨hKne, e1, -, hodd⟩ := head_facts K hK
    rw [e1, hO, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, by omega⟩, hodd⟩
    rw [← memS, ← List.flatten_splitBy r S]
    exact List.mem_flatten.mpr ⟨K, hK, List.head_mem hKne⟩
  have hOH : ∀ o ∈ O, (∀ d, d ∣ m → ¬ (d < o ∧ o < 2 * d)) → o ∈ H.toFinset := by
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
  have hHno : ∀ o ∈ H.toFinset, ∀ d, d ∣ m → ¬ (d < o ∧ o < 2 * d) := by
    intro o ho
    simp only [List.mem_toFinset, hH, List.mem_map] at ho
    obtain ⟨K, hK, rfl⟩ := ho
    obtain ⟨hKne, e1, hgap, -⟩ := head_facts K hK
    rw [e1]; exact hgap
  have hcardH : H.toFinset.card = H.length := List.toFinset_card_of_nodup hHnd
  rw [hTD, oddDivisorCount, ← hO, ← hcardH]
  constructor
  · intro hnp
    congr 1
    apply Finset.Subset.antisymm _ hHO
    intro o ho
    exact hOH o ho fun d hd h => hnp ⟨d, o, hd, (Nat.mem_divisors.mp (Finset.mem_filter.mp ho).1).1, h.1, h.2⟩
  · intro hc
    have hEq : H.toFinset = O := Finset.eq_of_subset_of_card_le hHO (by omega)
    rintro ⟨d, e, hd, he, hde, hed⟩
    obtain ⟨d', o, hd', ho, hoo, h1, h2⟩ := odd_pair hm e d hd he hde hed
    have hoO : o ∈ O := by rw [hO, Finset.mem_filter, Nat.mem_divisors]; exact ⟨⟨ho, by omega⟩, hoo⟩
    rw [← hEq] at hoO
    exact hHno o hoO d' hd' ⟨h1, h2⟩

end OMA.W2_a174905

open OMA.W2_a174905 in
theorem OMA.solution : type_of% @OMA.S_oeis_a174905.main := fun m hm => key m hm
