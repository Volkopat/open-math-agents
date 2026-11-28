import OMAStatements.S_oeis_a401248

-- Problem: A401248: Minimum number of terms in a 2-dense sublist of divisors of n (Pol's Conjecture 1).
-- Upstream: formal-conjectures statements/oeis-a401248.lean:0 (declaration OMA.S_oeis_a401248.main)
-- Credit: @nerotulip90 (the owner of the agent is credited as the solver)
-- Proof: let B be the first 2-dense block (it starts at 1 and is an initial segment of the divisors,
-- so closed under taking divisors). If another block K starts at d (no divisor in [d/2, d)), then every
-- a in B is coprime to d: for a prime p | a, its predecessor b in B has p <= 2b and b*d | n by induction,
-- so p | d would put the divisor (d/p)*b in [d/2, d). Hence a*d | n, and by induction a*d <= last(K)
-- (else the next divisor after K would be <= 2*last(K)). So a |-> a*d injects B into K.


namespace OMA.W2_a401248

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

open OMA.S_oeis_a401248

lemma length_le_of_map {B K : List ℕ} {d : ℕ} (hd : 0 < d) (hB : B.Nodup) (hK : K.Nodup)
    (h : ∀ a ∈ B, a * d ∈ K) : B.length ≤ K.length := by
  have hBm : (B.map (· * d)).Nodup := hB.map (fun x y hxy => by
    simpa [Nat.mul_left_inj hd.ne'] using hxy)
  rw [← List.length_map (f := (· * d)), ← List.toFinset_card_of_nodup hBm,
    ← List.toFinset_card_of_nodup hK]
  apply Finset.card_le_card
  intro x hx
  simp only [List.mem_toFinset, List.mem_map] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact h a ha

lemma main_ineq {n : ℕ} (hn : 1 ≤ n) {P T : List (List ℕ)} {K B : List ℕ} {rest : List (List ℕ)}
    (hb : blocks n = P ++ K :: T) (hb1 : blocks n = B :: rest) : B.length ≤ K.length := by
  set S := n.divisors.sort (· ≤ ·) with hSdef
  have hS : S.Pairwise (· < ·) := by
    have h1 := Finset.pairwise_sort n.divisors (· ≤ ·)
    have h2 := Finset.sort_nodup n.divisors (· ≤ ·)
    exact (h1.and h2).imp fun h => lt_of_le_of_ne h.1 h.2
  have memS : ∀ x, x ∈ S ↔ x ∣ n := fun x => by
    rw [Finset.mem_sort, Nat.mem_divisors]; exact ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
  have hbK : S.splitBy r = P ++ K :: T := hb
  have hbB : S.splitBy r = [] ++ B :: rest := hb1
  have hSne : S ≠ [] := fun h => by
    have := (memS 1).mpr (one_dvd n); rw [h] at this; simp at this
  -- the head of S is 1
  have hheadS : S.head hSne = 1 := by
    have h1 := head_le_of_pw hS hSne ((memS 1).mpr (one_dvd n))
    have h2 : 0 < S.head hSne := Nat.pos_of_dvd_of_pos ((memS _).mp (List.head_mem hSne)) (by omega)
    omega
  have hBne := K_ne hS hbB
  have hBhead : B.head hBne = 1 := by
    have := List.head_head_splitBy r hSne
    simp only [hbB, List.nil_append, List.head_cons] at this
    rw [this, hheadS]
  have hBmem : ∀ a, a ∣ n → a ≤ B.getLast hBne → a ∈ B := fun a ha hle =>
    mem_K_of_between hS hbB ((memS a).mpr ha)
      (by rw [hBhead]; exact Nat.pos_of_dvd_of_pos ha (by omega)) hle
  have hBS : ∀ a ∈ B, a ∈ S := fun a ha => by rw [l_eq hS hbB]; simp [ha]
  have hBpred : ∀ a ∈ B, a ≠ 1 → ∃ b ∈ B, b < a ∧ a ≤ 2 * b := fun a ha ha1 =>
    pred_exists (K_pw hS hbB) (K_chain hS hbB) hBne ha (by rw [hBhead]; exact ha1)
  rcases P.eq_nil_or_concat with hP | ⟨P', Q, hP⟩
  · subst hP
    have : B = K := by rw [hb1] at hb; simp at hb; exact hb.1
    rw [this]
  have hPne : P ≠ [] := by rw [hP]; simp
  have hKne := K_ne hS hbK
  set d := K.head hKne with hd
  set e := K.getLast hKne with he
  have hdS : d ∈ S := by
    rw [l_eq hS hbK]; exact List.mem_append_left _ (List.mem_append_right _ (List.head_mem hKne))
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos ((memS d).mp hdS) (by omega)
  have hde : d ≤ e := le_getLast_of_pw (K_pw hS hbK) hKne (List.head_mem hKne)
  -- Claim 1: a * d ∣ n for a ∈ B
  have claim1 : ∀ a, a ∈ B → a * d ∣ n := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha
      have hcop : Nat.Coprime a d := by
        apply Nat.coprime_of_dvd
        intro p hp hpa hpd
        have hpB : p ∈ B := hBmem p (hpa.trans ((memS a).mp (hBS a ha)))
          ((Nat.le_of_dvd (Nat.pos_of_dvd_of_pos ((memS a).mp (hBS a ha)) (by omega)) hpa).trans
            (le_getLast_of_pw (K_pw hS hbB) hBne ha))
        obtain ⟨b, hbB', hbp, hpb⟩ := hBpred p hpB hp.one_lt.ne'
        have hapos : 0 < a := Nat.pos_of_dvd_of_pos ((memS a).mp (hBS a ha)) (by omega) |>.trans_le' le_rfl
        have hba : b < a := lt_of_lt_of_le hbp (Nat.le_of_dvd hapos hpa)
        have hbd := ih b hba hbB'
        obtain ⟨d', hd'⟩ := hpd
        have hd'pos : 0 < d' := by
          rcases Nat.eq_zero_or_pos d' with h | h
          · rw [h, mul_zero] at hd'; omega
          · exact h
        have hyS : d' * b ∈ S := (memS _).mpr (Dvd.dvd.trans ⟨p, by rw [hd']; ring⟩ hbd)
        have hylt : d' * b < d := by rw [hd']; nlinarith
        have := gap_before hS hbK hPne hyS hylt
        rw [← hd, hd'] at this
        nlinarith
      exact hcop.mul_dvd_of_dvd_of_dvd ((memS a).mp (hBS a ha)) ((memS d).mp hdS)
  -- Claim 2: a * d ≤ e for a ∈ B
  have claim2 : ∀ a, a ∈ B → a * d ≤ e := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha
      by_cases ha1 : a = 1
      · subst ha1; simpa using hde
      obtain ⟨b, hbB', hba, hab⟩ := hBpred a ha ha1
      have hbd := ih b hba hbB'
      by_contra hgt
      push Not at hgt
      have hadS : a * d ∈ S := (memS _).mpr (claim1 a ha)
      rcases T.eq_nil_or_concat with hT | ⟨T', U, hT⟩
      · subst hT
        rw [l_eq hS hbK] at hadS
        simp only [List.flatten_nil, List.append_nil, List.mem_append] at hadS
        rcases hadS with h | h
        · have := lt_K hS hbK h (List.head_mem hKne); rw [← hd] at this; nlinarith
        · have := le_getLast_of_pw (K_pw hS hbK) hKne h; rw [← he] at this; omega
      · have hTne : T ≠ [] := by rw [hT]; simp
        have := gap_after hS hbK hTne hadS hgt
        nlinarith
  have hKnd : K.Nodup := (K_pw hS hbK).imp ne_of_lt
  have hBnd : B.Nodup := (K_pw hS hbB).imp ne_of_lt
  exact length_le_of_map hdpos hBnd hKnd fun a ha =>
    mem_K_of_between hS hbK ((memS _).mpr (claim1 a ha)) (by rw [← hd]; nlinarith [Nat.pos_of_ne_zero (show a ≠ 0 by rintro rfl; have := hBS 0 ha; rw [memS] at this; simp at this; omega)]) (claim2 a ha)

end OMA.W2_a401248

open OMA.W2_a401248 OMA.S_oeis_a401248 in
theorem OMA.solution : type_of% @OMA.S_oeis_a401248.main := by
  intro n hn
  have hne : blocks n ≠ [] := by
    unfold blocks
    rw [Ne, List.splitBy_eq_nil]
    intro h
    have : 1 ∈ n.divisors.sort (· ≤ ·) := by
      rw [Finset.mem_sort, Nat.mem_divisors]; exact ⟨one_dvd n, by omega⟩
    rw [h] at this; simp at this
  obtain ⟨B, rest, hb1⟩ := List.exists_cons_of_ne_nil hne
  have h1 : A384222 n 1 = B.length := by simp [A384222, hb1]
  rw [h1, A401248]
  have : ((blocks n).map List.length).min? = some B.length := by
    rw [List.min?_eq_some_iff]
    refine ⟨by rw [hb1]; simp, ?_⟩
    intro x hx
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hx
    obtain ⟨P, T, hPT⟩ := List.append_of_mem hK
    exact main_ineq hn hPT hb1
  rw [this]; rfl
