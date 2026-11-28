import OMAReductions.R_oeis_a003459_R1

namespace OMA.Proof_oeis_a003459_R1_H1

open OMA.S_oeis_a003459

private lemma digits_ne_nil_of_ge_ten {p : ℕ} (hp : 10 ≤ p) :
    2 ≤ (Nat.digits 10 p).length := by
  have hlt : ¬ (Nat.digits 10 p).length < 2 := by
    intro h
    have hpow := Nat.ofDigits_lt_base_pow_length (b := 10) (l := Nat.digits 10 p)
      (by decide) (fun x hx => Nat.digits_lt_base (by decide) hx)
    rw [Nat.ofDigits_digits] at hpow
    have h10 : 10 ^ (Nat.digits 10 p).length ≤ 10 := by
      have hle : (Nat.digits 10 p).length ≤ 1 := by omega
      calc 10 ^ (Nat.digits 10 p).length ≤ 10 ^ 1 := Nat.pow_le_pow_right (by decide) hle
        _ = 10 := by decide
    omega
  omega

private lemma ofDigits_ge_ten_of_pos_digits {l : List ℕ} (hlen : 2 ≤ l.length)
    (hpos : ∀ j ∈ l, 1 ≤ j) : 10 ≤ Nat.ofDigits 10 l := by
  match l with
  | [] => simp at hlen
  | [_] => simp at hlen
  | a :: b :: rest =>
    have ha : 1 ≤ a := hpos a (by simp)
    have hb : 1 ≤ b := hpos b (by simp)
    simp only [Nat.ofDigits_cons]
    omega

private lemma digits_admissible {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p) :
    ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9] := by
  have hlen : 2 ≤ (Nat.digits 10 p).length := digits_ne_nil_of_ge_ten hp
  have hzero : 0 ∉ Nat.digits 10 p := by
    intro h0
    have hp0 : (0 :: (Nat.digits 10 p).erase 0).Perm (Nat.digits 10 p) :=
      (List.perm_cons_erase h0).symm
    have hpr := hperm _ hp0
    rw [Nat.ofDigits_cons, zero_add] at hpr
    have h2 : 2 ∣ 10 * Nat.ofDigits 10 ((Nat.digits 10 p).erase 0) :=
      ⟨5 * Nat.ofDigits 10 ((Nat.digits 10 p).erase 0), by ring⟩
    have h5 : 5 ∣ 10 * Nat.ofDigits 10 ((Nat.digits 10 p).erase 0) :=
      ⟨2 * Nat.ofDigits 10 ((Nat.digits 10 p).erase 0), by ring⟩
    have heq2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).mp h2
    have heq5 := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) hpr).mp h5
    omega
  have hpos : ∀ j ∈ Nat.digits 10 p, 1 ≤ j := by
    intro j hj
    by_contra hlt
    have hj0 : j = 0 := by omega
    exact hzero (hj0 ▸ hj)
  intro j hj
  have hjlt : j < 10 := Nat.digits_lt_base (by decide) hj
  have hpj : (j :: (Nat.digits 10 p).erase j).Perm (Nat.digits 10 p) :=
    (List.perm_cons_erase hj).symm
  have hpr := hperm _ hpj
  have hge10 : 10 ≤ Nat.ofDigits 10 (j :: (Nat.digits 10 p).erase j) := by
    apply ofDigits_ge_ten_of_pos_digits
    · rw [hpj.length_eq]; exact hlen
    · intro x hx; exact hpos x (hpj.subset hx)
  have hnot2 : ¬ 2 ∣ Nat.ofDigits 10 (j :: (Nat.digits 10 p).erase j) := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).mp hd
    omega
  have hnot5 : ¬ 5 ∣ Nat.ofDigits 10 (j :: (Nat.digits 10 p).erase j) := by
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) hpr).mp hd
    omega
  rw [Nat.ofDigits_cons] at hnot2 hnot5
  have hmod2 : j % 2 ≠ 0 := by
    intro hm
    apply hnot2
    exact ⟨j / 2 + 5 * Nat.ofDigits 10 ((Nat.digits 10 p).erase j), by omega⟩
  have hmod5 : j % 5 ≠ 0 := by
    intro hm
    apply hnot5
    exact ⟨j / 5 + 2 * Nat.ofDigits 10 ((Nat.digits 10 p).erase j), by omega⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private lemma perm_canonical (d : List ℕ) (hadm : ∀ j ∈ d, j ∈ [1, 3, 7, 9]) :
    d.Perm (List.replicate (d.count 1) 1 ++ List.replicate (d.count 3) 3 ++
      List.replicate (d.count 7) 7 ++ List.replicate (d.count 9) 9) := by
  rw [List.perm_iff_count]
  intro x
  simp only [List.count_append, List.count_replicate]
  by_cases hx1 : x = 1
  · subst hx1; simp
  by_cases hx3 : x = 3
  · subst hx3; simp
  by_cases hx7 : x = 7
  · subst hx7; simp
  by_cases hx9 : x = 9
  · subst hx9; simp
  have hnot : x ∉ d := fun hm => by
    have := hadm x hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  rw [List.count_eq_zero.mpr hnot]
  simp only [beq_iff_eq]
  rw [if_neg (Ne.symm hx1), if_neg (Ne.symm hx3), if_neg (Ne.symm hx7), if_neg (Ne.symm hx9)]

private lemma length_eq_sum_counts (d : List ℕ) (hadm : ∀ j ∈ d, j ∈ [1, 3, 7, 9]) :
    d.length = d.count 1 + d.count 3 + d.count 7 + d.count 9 := by
  have hp := (perm_canonical d hadm).length_eq
  simp only [List.length_append, List.length_replicate] at hp
  omega

private lemma exists_submultiset (d : List ℕ) (hadm : ∀ j ∈ d, j ∈ [1, 3, 7, 9])
    (a1 a3 a7 a9 : ℕ)
    (h1 : a1 ≤ d.count 1) (h3 : a3 ≤ d.count 3) (h7 : a7 ≤ d.count 7) (h9 : a9 ≤ d.count 9) :
    ∃ rem : List ℕ, ((List.replicate a1 1 ++ List.replicate a3 3 ++
      List.replicate a7 7 ++ List.replicate a9 9) ++ rem).Perm d := by
  refine ⟨List.replicate (d.count 1 - a1) 1 ++ List.replicate (d.count 3 - a3) 3 ++
    List.replicate (d.count 7 - a7) 7 ++ List.replicate (d.count 9 - a9) 9, ?_⟩
  apply List.Perm.trans _ (perm_canonical d hadm).symm
  rw [List.perm_iff_count]
  intro x
  simp only [List.count_append, List.count_replicate]
  split_ifs <;> omega

private def isGoodCounts (c1 c3 c7 c9 : ℕ) (u : List ℕ) : Bool :=
  (u.all fun j => j == 1 || j == 3 || j == 7 || j == 9) &&
  (u.count 1 == c1) && (u.count 3 == c3) && (u.count 7 == c7) && (u.count 9 == c9)

private lemma perm_of_isGoodCounts {c1 c3 c7 c9 : ℕ} {u : List ℕ}
    (h : isGoodCounts c1 c3 c7 c9 u = true) :
    u.Perm (List.replicate c1 1 ++ List.replicate c3 3 ++
      List.replicate c7 7 ++ List.replicate c9 9) := by
  unfold isGoodCounts at h
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hall, h1⟩, h3⟩, h7⟩, h9⟩ := h
  have hadm : ∀ j ∈ u, j ∈ [1, 3, 7, 9] := by
    intro j hj
    have := hall j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have hcan := perm_canonical u hadm
  rwa [h1, h3, h7, h9] at hcan

private lemma not_perm_of_composite {p : ℕ} (hperm : IsPermutablePrime p)
    {w : List ℕ} (hw : w.Perm (Nat.digits 10 p)) (a b : ℕ)
    (ha : 1 < a) (hb : 1 < b) (hmul : Nat.ofDigits 10 w = a * b) : False := by
  have hpr := hperm w hw
  rw [hmul] at hpr
  exact Nat.not_prime_mul (by omega) (by omega) hpr

private lemma not_submultiset_of_mod7_cover {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (m : List ℕ) (hsub : ∃ rem : List ℕ, (m ++ rem).Perm (Nat.digits 10 p))
    (hcov : ∀ r : Fin 7, ∃ u : List ℕ, u.Perm m ∧ Nat.ofDigits 10 u % 7 = r.val) : False := by
  obtain ⟨rem, hrem⟩ := hsub
  let t : ℕ := (7 - (10 ^ m.length * Nat.ofDigits 10 rem) % 7) % 7
  have ht : t < 7 := Nat.mod_lt _ (by decide)
  obtain ⟨u, hum, hu7⟩ := hcov ⟨t, ht⟩
  have hpu : (u ++ rem).Perm (Nat.digits 10 p) := (hum.append_right rem).trans hrem
  have hpr := hperm (u ++ rem) hpu
  have hge10 : 10 ≤ Nat.ofDigits 10 (u ++ rem) := by
    apply ofDigits_ge_ten_of_pos_digits
    · rw [hpu.length_eq]; exact digits_ne_nil_of_ge_ten hp
    · intro x hx
      have := hadm x (hpu.subset hx)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      omega
  have hmod : Nat.ofDigits 10 (u ++ rem) % 7 = 0 := by
    rw [Nat.ofDigits_append, hum.length_eq, Nat.add_mod, hu7]
    dsimp only [t]
    omega
  have hdvd : 7 ∣ Nat.ofDigits 10 (u ++ rem) := Nat.dvd_of_mod_eq_zero hmod
  have heq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) hpr).mp hdvd
  omega

private def checkMod7 (c1 c3 c7 c9 : ℕ) (ws : List (List ℕ)) : Bool :=
  ws.length == 7 &&
  (List.finRange 7).all fun r =>
    let u := ws.getD r.val []
    isGoodCounts c1 c3 c7 c9 u && (Nat.ofDigits 10 u % 7 == r.val)

private lemma cover_of_checkMod7 {c1 c3 c7 c9 : ℕ} {ws : List (List ℕ)}
    (h : checkMod7 c1 c3 c7 c9 ws = true) :
    ∀ r : Fin 7, ∃ u : List ℕ,
      u.Perm (List.replicate c1 1 ++ List.replicate c3 3 ++ List.replicate c7 7 ++ List.replicate c9 9) ∧
      Nat.ofDigits 10 u % 7 = r.val := by
  unfold checkMod7 at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  intro r
  obtain ⟨hgood, hmod⟩ := h.2 r
  exact ⟨ws.getD r.val [], perm_of_isGoodCounts hgood, hmod⟩

private lemma exact_case {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (c1 c3 c7 c9 : ℕ)
    (h1 : (Nat.digits 10 p).count 1 = c1) (h3 : (Nat.digits 10 p).count 3 = c3)
    (h7 : (Nat.digits 10 p).count 7 = c7) (h9 : (Nat.digits 10 p).count 9 = c9)
    (w : List ℕ) (a b : ℕ) (ha : 1 < a) (hb : 1 < b)
    (hgood : isGoodCounts c1 c3 c7 c9 w = true)
    (hmul : Nat.ofDigits 10 w = a * b) : False := by
  have hcan := perm_canonical (Nat.digits 10 p) hadm
  rw [h1, h3, h7, h9] at hcan
  exact not_perm_of_composite hperm ((perm_of_isGoodCounts hgood).trans hcan.symm) a b ha hb hmul

private lemma cover_case {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (a1 a3 a7 a9 : ℕ)
    (h1 : a1 ≤ (Nat.digits 10 p).count 1) (h3 : a3 ≤ (Nat.digits 10 p).count 3)
    (h7 : a7 ≤ (Nat.digits 10 p).count 7) (h9 : a9 ≤ (Nat.digits 10 p).count 9)
    (ws : List (List ℕ))
    (hchk : checkMod7 a1 a3 a7 a9 ws = true) :
    False := by
  exact not_submultiset_of_mod7_cover hp hperm hadm _
    (exists_submultiset (Nat.digits 10 p) hadm a1 a3 a7 a9 h1 h3 h7 h9)
    (cover_of_checkMod7 hchk)

private lemma ex_0_1_1_1 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 0) (h3 : (Nat.digits 10 p).count 3 = 1)
    (h7 : (Nat.digits 10 p).count 7 = 1) (h9 : (Nat.digits 10 p).count 9 = 1) : False :=
  exact_case hperm hadm 0 1 1 1 h1 h3 h7 h9 [3, 7, 9] 7 139 (by decide) (by decide) (by decide) (by decide)
private lemma ex_1_0_1_1 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 1) (h3 : (Nat.digits 10 p).count 3 = 0)
    (h7 : (Nat.digits 10 p).count 7 = 1) (h9 : (Nat.digits 10 p).count 9 = 1) : False :=
  exact_case hperm hadm 1 0 1 1 h1 h3 h7 h9 [1, 9, 7] 7 113 (by decide) (by decide) (by decide) (by decide)
private lemma ex_1_1_0_1 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 1) (h3 : (Nat.digits 10 p).count 3 = 1)
    (h7 : (Nat.digits 10 p).count 7 = 0) (h9 : (Nat.digits 10 p).count 9 = 1) : False :=
  exact_case hperm hadm 1 1 0 1 h1 h3 h7 h9 [1, 3, 9] 7 133 (by decide) (by decide) (by decide) (by decide)
private lemma ex_1_1_1_0 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 1) (h3 : (Nat.digits 10 p).count 3 = 1)
    (h7 : (Nat.digits 10 p).count 7 = 1) (h9 : (Nat.digits 10 p).count 9 = 0) : False :=
  exact_case hperm hadm 1 1 1 0 h1 h3 h7 h9 [1, 3, 7] 17 43 (by decide) (by decide) (by decide) (by decide)
private lemma ex_0_0_2_2 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 0) (h3 : (Nat.digits 10 p).count 3 = 0)
    (h7 : (Nat.digits 10 p).count 7 = 2) (h9 : (Nat.digits 10 p).count 9 = 2) : False :=
  exact_case hperm hadm 0 0 2 2 h1 h3 h7 h9 [7, 7, 9, 9] 11 907 (by decide) (by decide) (by decide) (by decide)
private lemma ex_0_1_1_2 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 0) (h3 : (Nat.digits 10 p).count 3 = 1)
    (h7 : (Nat.digits 10 p).count 7 = 1) (h9 : (Nat.digits 10 p).count 9 = 2) : False :=
  exact_case hperm hadm 0 1 1 2 h1 h3 h7 h9 [3, 9, 7, 9] 7 1399 (by decide) (by decide) (by decide) (by decide)
private lemma ex_0_1_2_1 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 0) (h3 : (Nat.digits 10 p).count 3 = 1)
    (h7 : (Nat.digits 10 p).count 7 = 2) (h9 : (Nat.digits 10 p).count 9 = 1) : False :=
  exact_case hperm hadm 0 1 2 1 h1 h3 h7 h9 [3, 7, 7, 9] 29 337 (by decide) (by decide) (by decide) (by decide)
private lemma ex_0_2_0_2 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 0) (h3 : (Nat.digits 10 p).count 3 = 2)
    (h7 : (Nat.digits 10 p).count 7 = 0) (h9 : (Nat.digits 10 p).count 9 = 2) : False :=
  exact_case hperm hadm 0 2 0 2 h1 h3 h7 h9 [3, 3, 9, 9] 3 3311 (by decide) (by decide) (by decide) (by decide)
private lemma ex_0_2_1_1 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 0) (h3 : (Nat.digits 10 p).count 3 = 2)
    (h7 : (Nat.digits 10 p).count 7 = 1) (h9 : (Nat.digits 10 p).count 9 = 1) : False :=
  exact_case hperm hadm 0 2 1 1 h1 h3 h7 h9 [3, 7, 3, 9] 7 1339 (by decide) (by decide) (by decide) (by decide)
private lemma ex_0_2_2_0 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 0) (h3 : (Nat.digits 10 p).count 3 = 2)
    (h7 : (Nat.digits 10 p).count 7 = 2) (h9 : (Nat.digits 10 p).count 9 = 0) : False :=
  exact_case hperm hadm 0 2 2 0 h1 h3 h7 h9 [3, 3, 7, 7] 11 703 (by decide) (by decide) (by decide) (by decide)
private lemma ex_1_0_1_2 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 1) (h3 : (Nat.digits 10 p).count 3 = 0)
    (h7 : (Nat.digits 10 p).count 7 = 1) (h9 : (Nat.digits 10 p).count 9 = 2) : False :=
  exact_case hperm hadm 1 0 1 2 h1 h3 h7 h9 [1, 7, 9, 9] 13 767 (by decide) (by decide) (by decide) (by decide)
private lemma ex_1_0_2_1 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 1) (h3 : (Nat.digits 10 p).count 3 = 0)
    (h7 : (Nat.digits 10 p).count 7 = 2) (h9 : (Nat.digits 10 p).count 9 = 1) : False :=
  exact_case hperm hadm 1 0 2 1 h1 h3 h7 h9 [1, 7, 7, 9] 3 3257 (by decide) (by decide) (by decide) (by decide)
private lemma ex_1_1_0_2 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 1) (h3 : (Nat.digits 10 p).count 3 = 1)
    (h7 : (Nat.digits 10 p).count 7 = 0) (h9 : (Nat.digits 10 p).count 9 = 2) : False :=
  exact_case hperm hadm 1 1 0 2 h1 h3 h7 h9 [1, 9, 9, 3] 13 307 (by decide) (by decide) (by decide) (by decide)
private lemma ex_1_1_2_0 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 1) (h3 : (Nat.digits 10 p).count 3 = 1)
    (h7 : (Nat.digits 10 p).count 7 = 2) (h9 : (Nat.digits 10 p).count 9 = 0) : False :=
  exact_case hperm hadm 1 1 2 0 h1 h3 h7 h9 [1, 3, 7, 7] 3 2577 (by decide) (by decide) (by decide) (by decide)
private lemma ex_1_2_0_1 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 1) (h3 : (Nat.digits 10 p).count 3 = 2)
    (h7 : (Nat.digits 10 p).count 7 = 0) (h9 : (Nat.digits 10 p).count 9 = 1) : False :=
  exact_case hperm hadm 1 2 0 1 h1 h3 h7 h9 [1, 3, 3, 9] 7 1333 (by decide) (by decide) (by decide) (by decide)
private lemma ex_1_2_1_0 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 1) (h3 : (Nat.digits 10 p).count 3 = 2)
    (h7 : (Nat.digits 10 p).count 7 = 1) (h9 : (Nat.digits 10 p).count 9 = 0) : False :=
  exact_case hperm hadm 1 2 1 0 h1 h3 h7 h9 [1, 3, 7, 3] 7 533 (by decide) (by decide) (by decide) (by decide)
private lemma ex_2_0_0_2 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 2) (h3 : (Nat.digits 10 p).count 3 = 0)
    (h7 : (Nat.digits 10 p).count 7 = 0) (h9 : (Nat.digits 10 p).count 9 = 2) : False :=
  exact_case hperm hadm 2 0 0 2 h1 h3 h7 h9 [1, 1, 9, 9] 11 901 (by decide) (by decide) (by decide) (by decide)
private lemma ex_2_0_1_1 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 2) (h3 : (Nat.digits 10 p).count 3 = 0)
    (h7 : (Nat.digits 10 p).count 7 = 1) (h9 : (Nat.digits 10 p).count 9 = 1) : False :=
  exact_case hperm hadm 2 0 1 1 h1 h3 h7 h9 [1, 1, 7, 9] 3 3237 (by decide) (by decide) (by decide) (by decide)
private lemma ex_2_0_2_0 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 2) (h3 : (Nat.digits 10 p).count 3 = 0)
    (h7 : (Nat.digits 10 p).count 7 = 2) (h9 : (Nat.digits 10 p).count 9 = 0) : False :=
  exact_case hperm hadm 2 0 2 0 h1 h3 h7 h9 [1, 1, 7, 7] 11 701 (by decide) (by decide) (by decide) (by decide)
private lemma ex_2_1_0_1 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 2) (h3 : (Nat.digits 10 p).count 3 = 1)
    (h7 : (Nat.digits 10 p).count 7 = 0) (h9 : (Nat.digits 10 p).count 9 = 1) : False :=
  exact_case hperm hadm 2 1 0 1 h1 h3 h7 h9 [1, 3, 1, 9] 23 397 (by decide) (by decide) (by decide) (by decide)
private lemma ex_2_1_1_0 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 2) (h3 : (Nat.digits 10 p).count 3 = 1)
    (h7 : (Nat.digits 10 p).count 7 = 1) (h9 : (Nat.digits 10 p).count 9 = 0) : False :=
  exact_case hperm hadm 2 1 1 0 h1 h3 h7 h9 [1, 1, 3, 7] 3 2437 (by decide) (by decide) (by decide) (by decide)
private lemma ex_2_2_0_0 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 2) (h3 : (Nat.digits 10 p).count 3 = 2)
    (h7 : (Nat.digits 10 p).count 7 = 0) (h9 : (Nat.digits 10 p).count 9 = 0) : False :=
  exact_case hperm hadm 2 2 0 0 h1 h3 h7 h9 [1, 1, 3, 3] 7 473 (by decide) (by decide) (by decide) (by decide)
private lemma ex_3_0_1_1 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 3) (h3 : (Nat.digits 10 p).count 3 = 0)
    (h7 : (Nat.digits 10 p).count 7 = 1) (h9 : (Nat.digits 10 p).count 9 = 1) : False :=
  exact_case hperm hadm 3 0 1 1 h1 h3 h7 h9 [1, 1, 1, 7, 9] 7 13873 (by decide) (by decide) (by decide) (by decide)
private lemma ex_1_1_0_3 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 1) (h3 : (Nat.digits 10 p).count 3 = 1)
    (h7 : (Nat.digits 10 p).count 7 = 0) (h9 : (Nat.digits 10 p).count 9 = 3) : False :=
  exact_case hperm hadm 1 1 0 3 h1 h3 h7 h9 [1, 3, 9, 9, 9] 13 7687 (by decide) (by decide) (by decide) (by decide)
private lemma ex_4_0_1_1 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 4) (h3 : (Nat.digits 10 p).count 3 = 0)
    (h7 : (Nat.digits 10 p).count 7 = 1) (h9 : (Nat.digits 10 p).count 9 = 1) : False :=
  exact_case hperm hadm 4 0 1 1 h1 h3 h7 h9 [1, 1, 1, 7, 1, 9] 13 70547 (by decide) (by decide) (by decide) (by decide)
private lemma ex_1_1_0_4 {p : ℕ} (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : (Nat.digits 10 p).count 1 = 1) (h3 : (Nat.digits 10 p).count 3 = 1)
    (h7 : (Nat.digits 10 p).count 7 = 0) (h9 : (Nat.digits 10 p).count 9 = 4) : False :=
  exact_case hperm hadm 1 1 0 4 h1 h3 h7 h9 [1, 9, 3, 9, 9, 9] 97 10303 (by decide) (by decide) (by decide) (by decide)

private lemma cov_1_1_1_1 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 1 ≤ (Nat.digits 10 p).count 1) (h3 : 1 ≤ (Nat.digits 10 p).count 3)
    (h7 : 1 ≤ (Nat.digits 10 p).count 7) (h9 : 1 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 1 1 1 1 h1 h3 h7 h9 [[1, 3, 9, 7], [1, 3, 7, 9], [1, 7, 9, 3], [3, 1, 9, 7], [1, 9, 7, 3], [1, 7, 3, 9], [1, 9, 3, 7]] (by decide)
private lemma cov_3_2_0_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 3 ≤ (Nat.digits 10 p).count 1) (h3 : 2 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 3 2 0 0 h1 h3 h7 h9 [[1, 1, 3, 1, 3], [1, 1, 1, 3, 3], [1, 3, 1, 1, 3], [3, 3, 1, 1, 1], [1, 1, 3, 3, 1], [1, 3, 3, 1, 1], [1, 3, 1, 3, 1]] (by decide)
private lemma cov_3_0_2_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 3 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 2 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 3 0 2 0 h1 h3 h7 h9 [[1, 7, 1, 7, 1], [1, 1, 7, 7, 1], [1, 7, 1, 1, 7], [1, 1, 7, 1, 7], [1, 7, 7, 1, 1], [7, 7, 1, 1, 1], [1, 1, 1, 7, 7]] (by decide)
private lemma cov_3_0_0_2 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 3 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 2 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 3 0 0 2 h1 h3 h7 h9 [[1, 9, 9, 1, 1], [1, 1, 9, 1, 9], [1, 9, 1, 1, 9], [1, 1, 9, 9, 1], [1, 9, 1, 9, 1], [1, 1, 1, 9, 9], [9, 9, 1, 1, 1]] (by decide)
private lemma cov_2_3_0_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 2 ≤ (Nat.digits 10 p).count 1) (h3 : 3 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 2 3 0 0 h1 h3 h7 h9 [[1, 3, 1, 3, 3], [3, 3, 1, 3, 1], [3, 1, 3, 1, 3], [1, 3, 3, 3, 1], [3, 3, 1, 1, 3], [1, 1, 3, 3, 3], [1, 3, 3, 1, 3]] (by decide)
private lemma cov_0_3_2_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 3 ≤ (Nat.digits 10 p).count 3)
    (h7 : 2 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 3 2 0 h1 h3 h7 h9 [[3, 7, 3, 7, 3], [7, 7, 3, 3, 3], [3, 3, 7, 3, 7], [3, 3, 7, 7, 3], [3, 3, 3, 7, 7], [3, 7, 7, 3, 3], [3, 7, 3, 3, 7]] (by decide)
private lemma cov_0_3_0_2 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 3 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 2 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 3 0 2 h1 h3 h7 h9 [[3, 3, 9, 3, 9], [3, 9, 9, 3, 3], [9, 9, 3, 3, 3], [3, 3, 3, 9, 9], [3, 9, 3, 9, 3], [3, 3, 9, 9, 3], [3, 9, 3, 3, 9]] (by decide)
private lemma cov_2_0_3_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 2 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 3 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 2 0 3 0 h1 h3 h7 h9 [[1, 7, 7, 1, 7], [7, 7, 1, 1, 7], [7, 1, 7, 1, 7], [1, 7, 1, 7, 7], [1, 1, 7, 7, 7], [1, 7, 7, 7, 1], [7, 7, 1, 7, 1]] (by decide)
private lemma cov_0_2_3_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 2 ≤ (Nat.digits 10 p).count 3)
    (h7 : 3 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 2 3 0 h1 h3 h7 h9 [[3, 7, 7, 3, 7], [3, 7, 7, 7, 3], [3, 7, 3, 7, 7], [7, 7, 3, 3, 7], [7, 7, 3, 7, 3], [3, 3, 7, 7, 7], [7, 3, 7, 3, 7]] (by decide)
private lemma cov_0_0_3_2 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 3 ≤ (Nat.digits 10 p).count 7) (h9 : 2 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 0 3 2 h1 h3 h7 h9 [[7, 9, 7, 7, 9], [9, 9, 7, 7, 7], [7, 7, 9, 9, 7], [7, 9, 9, 7, 7], [7, 9, 7, 9, 7], [7, 7, 9, 7, 9], [7, 7, 7, 9, 9]] (by decide)
private lemma cov_2_0_0_3 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 2 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 3 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 2 0 0 3 h1 h3 h7 h9 [[1, 1, 9, 9, 9], [1, 9, 1, 9, 9], [9, 1, 9, 1, 9], [9, 9, 1, 1, 9], [1, 9, 9, 1, 9], [9, 9, 1, 9, 1], [1, 9, 9, 9, 1]] (by decide)
private lemma cov_0_2_0_3 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 2 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 3 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 2 0 3 h1 h3 h7 h9 [[3, 9, 3, 9, 9], [3, 3, 9, 9, 9], [3, 9, 9, 9, 3], [9, 9, 3, 9, 3], [3, 9, 9, 3, 9], [9, 9, 3, 3, 9], [9, 3, 9, 3, 9]] (by decide)
private lemma cov_0_0_2_3 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 2 ≤ (Nat.digits 10 p).count 7) (h9 : 3 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 0 2 3 h1 h3 h7 h9 [[9, 7, 9, 7, 9], [7, 9, 9, 9, 7], [9, 9, 7, 7, 9], [7, 7, 9, 9, 9], [7, 9, 9, 7, 9], [7, 9, 7, 9, 9], [9, 9, 7, 9, 7]] (by decide)
private lemma cov_2_2_1_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 2 ≤ (Nat.digits 10 p).count 1) (h3 : 2 ≤ (Nat.digits 10 p).count 3)
    (h7 : 1 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 2 2 1 0 h1 h3 h7 h9 [[1, 1, 3, 3, 7], [1, 1, 3, 7, 3], [1, 3, 1, 3, 7], [1, 3, 1, 7, 3], [1, 3, 7, 3, 1], [1, 7, 1, 3, 3], [1, 1, 7, 3, 3]] (by decide)
private lemma cov_2_2_0_1 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 2 ≤ (Nat.digits 10 p).count 1) (h3 : 2 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 1 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 2 2 0 1 h1 h3 h7 h9 [[1, 9, 3, 3, 1], [1, 1, 3, 3, 9], [1, 3, 3, 1, 9], [1, 1, 9, 3, 3], [1, 3, 3, 9, 1], [3, 1, 3, 1, 9], [1, 1, 3, 9, 3]] (by decide)
private lemma cov_2_1_2_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 2 ≤ (Nat.digits 10 p).count 1) (h3 : 1 ≤ (Nat.digits 10 p).count 3)
    (h7 : 2 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 2 1 2 0 h1 h3 h7 h9 [[1, 3, 7, 7, 1], [1, 1, 7, 3, 7], [1, 1, 7, 7, 3], [1, 1, 3, 7, 7], [1, 7, 3, 7, 1], [1, 3, 1, 7, 7], [1, 7, 3, 1, 7]] (by decide)
private lemma cov_2_0_2_1 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 2 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 2 ≤ (Nat.digits 10 p).count 7) (h9 : 1 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 2 0 2 1 h1 h3 h7 h9 [[7, 7, 9, 1, 1], [1, 1, 9, 7, 7], [1, 1, 7, 9, 7], [1, 7, 7, 9, 1], [1, 7, 1, 7, 9], [1, 1, 7, 7, 9], [1, 9, 7, 1, 7]] (by decide)
private lemma cov_2_1_0_2 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 2 ≤ (Nat.digits 10 p).count 1) (h3 : 1 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 2 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 2 1 0 2 h1 h3 h7 h9 [[1, 3, 9, 1, 9], [1, 9, 3, 9, 1], [1, 1, 3, 9, 9], [3, 1, 9, 1, 9], [1, 1, 9, 9, 3], [1, 9, 1, 9, 3], [1, 1, 9, 3, 9]] (by decide)
private lemma cov_2_0_1_2 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 2 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 1 ≤ (Nat.digits 10 p).count 7) (h9 : 2 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 2 0 1 2 h1 h3 h7 h9 [[1, 7, 9, 9, 1], [1, 9, 9, 7, 1], [1, 1, 9, 7, 9], [1, 1, 7, 9, 9], [7, 1, 1, 9, 9], [1, 7, 9, 1, 9], [1, 1, 9, 9, 7]] (by decide)
private lemma cov_1_2_2_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 1 ≤ (Nat.digits 10 p).count 1) (h3 : 2 ≤ (Nat.digits 10 p).count 3)
    (h7 : 2 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 1 2 2 0 h1 h3 h7 h9 [[1, 3, 7, 3, 7], [1, 3, 7, 7, 3], [1, 3, 3, 7, 7], [1, 7, 7, 3, 3], [1, 7, 3, 3, 7], [1, 7, 3, 7, 3], [3, 7, 3, 7, 1]] (by decide)
private lemma cov_0_2_2_1 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 2 ≤ (Nat.digits 10 p).count 3)
    (h7 : 2 ≤ (Nat.digits 10 p).count 7) (h9 : 1 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 2 2 1 h1 h3 h7 h9 [[3, 7, 3, 9, 7], [3, 7, 7, 3, 9], [3, 3, 9, 7, 7], [3, 3, 7, 9, 7], [3, 7, 9, 3, 7], [3, 7, 9, 7, 3], [3, 3, 7, 7, 9]] (by decide)
private lemma cov_1_2_0_2 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 1 ≤ (Nat.digits 10 p).count 1) (h3 : 2 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 2 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 1 2 0 2 h1 h3 h7 h9 [[3, 9, 1, 9, 3], [1, 3, 3, 9, 9], [1, 9, 3, 9, 3], [1, 3, 9, 9, 3], [1, 9, 3, 3, 9], [1, 3, 9, 3, 9], [1, 9, 9, 3, 3]] (by decide)
private lemma cov_0_2_1_2 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 2 ≤ (Nat.digits 10 p).count 3)
    (h7 : 1 ≤ (Nat.digits 10 p).count 7) (h9 : 2 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 2 1 2 h1 h3 h7 h9 [[3, 3, 9, 9, 7], [3, 7, 3, 9, 9], [3, 9, 3, 7, 9], [3, 3, 9, 7, 9], [3, 3, 7, 9, 9], [3, 7, 9, 3, 9], [3, 9, 3, 9, 7]] (by decide)
private lemma cov_1_0_2_2 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 1 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 2 ≤ (Nat.digits 10 p).count 7) (h9 : 2 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 1 0 2 2 h1 h3 h7 h9 [[1, 7, 7, 9, 9], [1, 9, 7, 7, 9], [7, 1, 7, 9, 9], [1, 7, 9, 9, 7], [1, 9, 9, 7, 7], [1, 9, 7, 9, 7], [1, 7, 9, 7, 9]] (by decide)
private lemma cov_0_1_2_2 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 1 ≤ (Nat.digits 10 p).count 3)
    (h7 : 2 ≤ (Nat.digits 10 p).count 7) (h9 : 2 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 1 2 2 h1 h3 h7 h9 [[3, 9, 7, 9, 7], [3, 7, 9, 7, 9], [3, 7, 7, 9, 9], [3, 9, 7, 7, 9], [7, 3, 9, 9, 7], [3, 7, 9, 9, 7], [3, 9, 9, 7, 7]] (by decide)
private lemma cov_3_1_1_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 3 ≤ (Nat.digits 10 p).count 1) (h3 : 1 ≤ (Nat.digits 10 p).count 3)
    (h7 : 1 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 3 1 1 0 h1 h3 h7 h9 [[1, 1, 3, 7, 1], [1, 1, 7, 1, 3], [1, 1, 3, 1, 7], [1, 1, 1, 3, 7], [1, 1, 1, 7, 3], [1, 1, 7, 3, 1], [1, 3, 7, 1, 1]] (by decide)
private lemma cov_3_1_0_1 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 3 ≤ (Nat.digits 10 p).count 1) (h3 : 1 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 1 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 3 1 0 1 h1 h3 h7 h9 [[1, 3, 1, 9, 1], [3, 1, 1, 1, 9], [1, 1, 1, 9, 3], [1, 1, 3, 1, 9], [1, 1, 1, 3, 9], [1, 1, 3, 9, 1], [1, 9, 1, 1, 3]] (by decide)
private lemma cov_1_3_1_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 1 ≤ (Nat.digits 10 p).count 1) (h3 : 3 ≤ (Nat.digits 10 p).count 3)
    (h7 : 1 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 1 3 1 0 h1 h3 h7 h9 [[1, 3, 3, 7, 3], [3, 1, 7, 3, 3], [1, 7, 3, 3, 3], [3, 1, 3, 7, 3], [3, 3, 1, 3, 7], [1, 3, 7, 3, 3], [1, 3, 3, 3, 7]] (by decide)
private lemma cov_1_3_0_1 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 1 ≤ (Nat.digits 10 p).count 1) (h3 : 3 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 1 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 1 3 0 1 h1 h3 h7 h9 [[1, 3, 3, 3, 9], [1, 9, 3, 3, 3], [1, 3, 9, 3, 3], [3, 1, 3, 3, 9], [3, 3, 3, 1, 9], [1, 3, 3, 9, 3], [3, 3, 3, 9, 1]] (by decide)
private lemma cov_0_3_1_1 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 3 ≤ (Nat.digits 10 p).count 3)
    (h7 : 1 ≤ (Nat.digits 10 p).count 7) (h9 : 1 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 3 1 1 h1 h3 h7 h9 [[3, 3, 9, 7, 3], [3, 3, 7, 9, 3], [3, 3, 3, 9, 7], [3, 3, 7, 3, 9], [3, 9, 7, 3, 3], [3, 3, 3, 7, 9], [3, 3, 9, 3, 7]] (by decide)
private lemma cov_1_1_3_0 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 1 ≤ (Nat.digits 10 p).count 1) (h3 : 1 ≤ (Nat.digits 10 p).count 3)
    (h7 : 3 ≤ (Nat.digits 10 p).count 7) (h9 : 0 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 1 1 3 0 h1 h3 h7 h9 [[1, 7, 3, 7, 7], [7, 1, 7, 7, 3], [3, 7, 7, 1, 7], [1, 3, 7, 7, 7], [7, 3, 1, 7, 7], [1, 7, 7, 3, 7], [1, 7, 7, 7, 3]] (by decide)
private lemma cov_1_0_3_1 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 1 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 3 ≤ (Nat.digits 10 p).count 7) (h9 : 1 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 1 0 3 1 h1 h3 h7 h9 [[1, 9, 7, 7, 7], [7, 1, 7, 9, 7], [1, 7, 7, 7, 9], [7, 7, 1, 7, 9], [7, 1, 7, 7, 9], [1, 7, 9, 7, 7], [1, 7, 7, 9, 7]] (by decide)
private lemma cov_0_1_3_1 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 1 ≤ (Nat.digits 10 p).count 3)
    (h7 : 3 ≤ (Nat.digits 10 p).count 7) (h9 : 1 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 1 3 1 h1 h3 h7 h9 [[3, 7, 9, 7, 7], [3, 7, 7, 9, 7], [3, 9, 7, 7, 7], [7, 3, 7, 7, 9], [3, 7, 7, 7, 9], [7, 7, 7, 3, 9], [7, 3, 9, 7, 7]] (by decide)
private lemma cov_1_0_1_3 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 1 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 1 ≤ (Nat.digits 10 p).count 7) (h9 : 3 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 1 0 1 3 h1 h3 h7 h9 [[7, 9, 1, 9, 9], [9, 7, 9, 9, 1], [1, 9, 9, 9, 7], [7, 9, 9, 1, 9], [1, 7, 9, 9, 9], [1, 9, 9, 7, 9], [1, 9, 7, 9, 9]] (by decide)
private lemma cov_0_1_1_3 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 0 ≤ (Nat.digits 10 p).count 1) (h3 : 1 ≤ (Nat.digits 10 p).count 3)
    (h7 : 1 ≤ (Nat.digits 10 p).count 7) (h9 : 3 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 0 1 1 3 h1 h3 h7 h9 [[3, 9, 9, 7, 9], [3, 9, 7, 9, 9], [9, 3, 9, 7, 9], [9, 3, 7, 9, 9], [3, 9, 9, 9, 7], [7, 3, 9, 9, 9], [3, 7, 9, 9, 9]] (by decide)
private lemma cov_5_0_1_1 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 5 ≤ (Nat.digits 10 p).count 1) (h3 : 0 ≤ (Nat.digits 10 p).count 3)
    (h7 : 1 ≤ (Nat.digits 10 p).count 7) (h9 : 1 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 5 0 1 1 h1 h3 h7 h9 [[1, 1, 1, 1, 9, 7, 1], [7, 1, 1, 1, 1, 1, 9], [1, 1, 1, 1, 7, 9, 1], [1, 1, 1, 7, 1, 1, 9], [1, 1, 1, 1, 1, 7, 9], [1, 1, 1, 1, 1, 9, 7], [1, 1, 1, 7, 9, 1, 1]] (by decide)
private lemma cov_1_1_0_5 {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (h1 : 1 ≤ (Nat.digits 10 p).count 1) (h3 : 1 ≤ (Nat.digits 10 p).count 3)
    (h7 : 0 ≤ (Nat.digits 10 p).count 7) (h9 : 5 ≤ (Nat.digits 10 p).count 9) : False :=
  cover_case hp hperm hadm 1 1 0 5 h1 h3 h7 h9 [[1, 9, 9, 3, 9, 9, 9], [3, 9, 1, 9, 9, 9, 9], [1, 9, 9, 9, 9, 9, 3], [1, 9, 3, 9, 9, 9, 9], [1, 3, 9, 9, 9, 9, 9], [1, 9, 9, 9, 3, 9, 9], [1, 9, 9, 9, 9, 3, 9]] (by decide)

private def coveredTuple (a b c d : ℕ) : Bool :=
  (1 ≤ a && 1 ≤ b && 1 ≤ c && 1 ≤ d) ||
  (3 ≤ a && 2 ≤ b) || (3 ≤ a && 2 ≤ c) || (3 ≤ a && 2 ≤ d) ||
  (2 ≤ a && 3 ≤ b) || (3 ≤ b && 2 ≤ c) || (3 ≤ b && 2 ≤ d) ||
  (2 ≤ a && 3 ≤ c) || (2 ≤ b && 3 ≤ c) || (3 ≤ c && 2 ≤ d) ||
  (2 ≤ a && 3 ≤ d) || (2 ≤ b && 3 ≤ d) || (2 ≤ c && 3 ≤ d) ||
  (2 ≤ a && 2 ≤ b && 1 ≤ c) || (2 ≤ a && 2 ≤ b && 1 ≤ d) ||
  (2 ≤ a && 1 ≤ b && 2 ≤ c) || (2 ≤ a && 2 ≤ c && 1 ≤ d) ||
  (2 ≤ a && 1 ≤ b && 2 ≤ d) || (2 ≤ a && 1 ≤ c && 2 ≤ d) ||
  (1 ≤ a && 2 ≤ b && 2 ≤ c) || (2 ≤ b && 2 ≤ c && 1 ≤ d) ||
  (1 ≤ a && 2 ≤ b && 2 ≤ d) || (2 ≤ b && 1 ≤ c && 2 ≤ d) ||
  (1 ≤ a && 2 ≤ c && 2 ≤ d) || (1 ≤ b && 2 ≤ c && 2 ≤ d) ||
  (3 ≤ a && 1 ≤ b && 1 ≤ c) || (3 ≤ a && 1 ≤ b && 1 ≤ d) ||
  (1 ≤ a && 3 ≤ b && 1 ≤ c) || (1 ≤ a && 3 ≤ b && 1 ≤ d) ||
  (3 ≤ b && 1 ≤ c && 1 ≤ d) || (1 ≤ a && 1 ≤ b && 3 ≤ c) ||
  (1 ≤ a && 3 ≤ c && 1 ≤ d) || (1 ≤ b && 3 ≤ c && 1 ≤ d) ||
  (1 ≤ a && 1 ≤ c && 3 ≤ d) || (1 ≤ b && 1 ≤ c && 3 ≤ d)

private def exactTupleList : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0,1,1,1), (1,0,1,1), (1,1,0,1), (1,1,1,0), (0,0,2,2), (0,1,1,2), (0,1,2,1), (0,2,0,2),
   (0,2,1,1), (0,2,2,0), (1,0,1,2), (1,0,2,1), (1,1,0,2), (1,1,2,0), (1,2,0,1), (1,2,1,0),
   (2,0,0,2), (2,0,1,1), (2,0,2,0), (2,1,0,1), (2,1,1,0), (2,2,0,0), (3,0,1,1), (1,1,0,3),
   (4,0,1,1), (1,1,0,4)]

private lemma small_tuple_exhaustive :
    ∀ a b c d : Fin 5,
      a.val + 2 ≤ a.val + b.val + c.val + d.val →
      b.val + 2 ≤ a.val + b.val + c.val + d.val →
      c.val + 2 ≤ a.val + b.val + c.val + d.val →
      d.val + 2 ≤ a.val + b.val + c.val + d.val →
      coveredTuple a.val b.val c.val d.val = false →
      (a.val, b.val, c.val, d.val) ∈ exactTupleList := by
  decide

private lemma no_multi_digits {p : ℕ} (hp : 10 ≤ p) (hperm : IsPermutablePrime p)
    (hadm : ∀ j ∈ Nat.digits 10 p, j ∈ [1, 3, 7, 9])
    (hn1 : (Nat.digits 10 p).count 1 + 2 ≤ (Nat.digits 10 p).length)
    (hn3 : (Nat.digits 10 p).count 3 + 2 ≤ (Nat.digits 10 p).length)
    (hn7 : (Nat.digits 10 p).count 7 + 2 ≤ (Nat.digits 10 p).length)
    (hn9 : (Nat.digits 10 p).count 9 + 2 ≤ (Nat.digits 10 p).length) : False := by
  set c1 := (Nat.digits 10 p).count 1
  set c3 := (Nat.digits 10 p).count 3
  set c7 := (Nat.digits 10 p).count 7
  set c9 := (Nat.digits 10 p).count 9
  have hL : (Nat.digits 10 p).length = c1 + c3 + c7 + c9 := length_eq_sum_counts _ hadm
  rw [hL] at hn1 hn3 hn7 hn9
  have hc_0 : ¬ (1 ≤ c1 ∧ 1 ≤ c3 ∧ 1 ≤ c7 ∧ 1 ≤ c9) := fun h =>
    cov_1_1_1_1 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_1 : ¬ (3 ≤ c1 ∧ 2 ≤ c3) := fun h =>
    cov_3_2_0_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_2 : ¬ (3 ≤ c1 ∧ 2 ≤ c7) := fun h =>
    cov_3_0_2_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_3 : ¬ (3 ≤ c1 ∧ 2 ≤ c9) := fun h =>
    cov_3_0_0_2 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_4 : ¬ (2 ≤ c1 ∧ 3 ≤ c3) := fun h =>
    cov_2_3_0_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_5 : ¬ (3 ≤ c3 ∧ 2 ≤ c7) := fun h =>
    cov_0_3_2_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_6 : ¬ (3 ≤ c3 ∧ 2 ≤ c9) := fun h =>
    cov_0_3_0_2 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_7 : ¬ (2 ≤ c1 ∧ 3 ≤ c7) := fun h =>
    cov_2_0_3_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_8 : ¬ (2 ≤ c3 ∧ 3 ≤ c7) := fun h =>
    cov_0_2_3_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_9 : ¬ (3 ≤ c7 ∧ 2 ≤ c9) := fun h =>
    cov_0_0_3_2 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_10 : ¬ (2 ≤ c1 ∧ 3 ≤ c9) := fun h =>
    cov_2_0_0_3 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_11 : ¬ (2 ≤ c3 ∧ 3 ≤ c9) := fun h =>
    cov_0_2_0_3 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_12 : ¬ (2 ≤ c7 ∧ 3 ≤ c9) := fun h =>
    cov_0_0_2_3 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_13 : ¬ (2 ≤ c1 ∧ 2 ≤ c3 ∧ 1 ≤ c7) := fun h =>
    cov_2_2_1_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_14 : ¬ (2 ≤ c1 ∧ 2 ≤ c3 ∧ 1 ≤ c9) := fun h =>
    cov_2_2_0_1 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_15 : ¬ (2 ≤ c1 ∧ 1 ≤ c3 ∧ 2 ≤ c7) := fun h =>
    cov_2_1_2_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_16 : ¬ (2 ≤ c1 ∧ 2 ≤ c7 ∧ 1 ≤ c9) := fun h =>
    cov_2_0_2_1 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_17 : ¬ (2 ≤ c1 ∧ 1 ≤ c3 ∧ 2 ≤ c9) := fun h =>
    cov_2_1_0_2 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_18 : ¬ (2 ≤ c1 ∧ 1 ≤ c7 ∧ 2 ≤ c9) := fun h =>
    cov_2_0_1_2 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_19 : ¬ (1 ≤ c1 ∧ 2 ≤ c3 ∧ 2 ≤ c7) := fun h =>
    cov_1_2_2_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_20 : ¬ (2 ≤ c3 ∧ 2 ≤ c7 ∧ 1 ≤ c9) := fun h =>
    cov_0_2_2_1 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_21 : ¬ (1 ≤ c1 ∧ 2 ≤ c3 ∧ 2 ≤ c9) := fun h =>
    cov_1_2_0_2 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_22 : ¬ (2 ≤ c3 ∧ 1 ≤ c7 ∧ 2 ≤ c9) := fun h =>
    cov_0_2_1_2 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_23 : ¬ (1 ≤ c1 ∧ 2 ≤ c7 ∧ 2 ≤ c9) := fun h =>
    cov_1_0_2_2 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_24 : ¬ (1 ≤ c3 ∧ 2 ≤ c7 ∧ 2 ≤ c9) := fun h =>
    cov_0_1_2_2 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_25 : ¬ (3 ≤ c1 ∧ 1 ≤ c3 ∧ 1 ≤ c7) := fun h =>
    cov_3_1_1_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_26 : ¬ (3 ≤ c1 ∧ 1 ≤ c3 ∧ 1 ≤ c9) := fun h =>
    cov_3_1_0_1 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_27 : ¬ (1 ≤ c1 ∧ 3 ≤ c3 ∧ 1 ≤ c7) := fun h =>
    cov_1_3_1_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_28 : ¬ (1 ≤ c1 ∧ 3 ≤ c3 ∧ 1 ≤ c9) := fun h =>
    cov_1_3_0_1 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_29 : ¬ (3 ≤ c3 ∧ 1 ≤ c7 ∧ 1 ≤ c9) := fun h =>
    cov_0_3_1_1 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_30 : ¬ (1 ≤ c1 ∧ 1 ≤ c3 ∧ 3 ≤ c7) := fun h =>
    cov_1_1_3_0 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_31 : ¬ (1 ≤ c1 ∧ 3 ≤ c7 ∧ 1 ≤ c9) := fun h =>
    cov_1_0_3_1 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_32 : ¬ (1 ≤ c3 ∧ 3 ≤ c7 ∧ 1 ≤ c9) := fun h =>
    cov_0_1_3_1 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_33 : ¬ (1 ≤ c1 ∧ 1 ≤ c7 ∧ 3 ≤ c9) := fun h =>
    cov_1_0_1_3 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_34 : ¬ (1 ≤ c3 ∧ 1 ≤ c7 ∧ 3 ≤ c9) := fun h =>
    cov_0_1_1_3 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_35 : ¬ (5 ≤ c1 ∧ 1 ≤ c7 ∧ 1 ≤ c9) := fun h =>
    cov_5_0_1_1 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hc_36 : ¬ (1 ≤ c1 ∧ 1 ≤ c3 ∧ 5 ≤ c9) := fun h =>
    cov_1_1_0_5 hp hperm hadm (by omega) (by omega) (by omega) (by omega)
  have hbound1 : c1 ≤ 4 := by
    by_contra h
    have hc1 : 5 ≤ c1 := by omega
    by_cases h3 : 1 ≤ c3
    · by_cases h7 : 1 ≤ c7
      · exact hc_25 ⟨by omega, h3, h7⟩
      · by_cases h9 : 1 ≤ c9
        · exact hc_26 ⟨by omega, h3, h9⟩
        · exact hc_1 ⟨by omega, by omega⟩
    · by_cases h7 : 1 ≤ c7
      · by_cases h9 : 1 ≤ c9
        · exact hc_35 ⟨hc1, h7, h9⟩
        · exact hc_2 ⟨by omega, by omega⟩
      · exact hc_3 ⟨by omega, by omega⟩
  have hbound3 : c3 ≤ 4 := by
    by_contra h
    have hc3 : 5 ≤ c3 := by omega
    by_cases h1 : 1 ≤ c1
    · by_cases h7 : 1 ≤ c7
      · exact hc_27 ⟨h1, by omega, h7⟩
      · by_cases h9 : 1 ≤ c9
        · exact hc_28 ⟨h1, by omega, h9⟩
        · exact hc_4 ⟨by omega, by omega⟩
    · by_cases h7 : 1 ≤ c7
      · by_cases h9 : 1 ≤ c9
        · exact hc_29 ⟨by omega, h7, h9⟩
        · exact hc_5 ⟨by omega, by omega⟩
      · exact hc_6 ⟨by omega, by omega⟩
  have hbound7 : c7 ≤ 4 := by
    by_contra h
    have hc7 : 5 ≤ c7 := by omega
    by_cases h1 : 1 ≤ c1
    · by_cases h3 : 1 ≤ c3
      · exact hc_30 ⟨h1, h3, by omega⟩
      · by_cases h9 : 1 ≤ c9
        · exact hc_31 ⟨h1, by omega, h9⟩
        · exact hc_7 ⟨by omega, by omega⟩
    · by_cases h3 : 1 ≤ c3
      · by_cases h9 : 1 ≤ c9
        · exact hc_32 ⟨h3, by omega, h9⟩
        · exact hc_8 ⟨by omega, by omega⟩
      · exact hc_9 ⟨by omega, by omega⟩
  have hbound9 : c9 ≤ 4 := by
    by_contra h
    have hc9 : 5 ≤ c9 := by omega
    by_cases h1 : 1 ≤ c1
    · by_cases h3 : 1 ≤ c3
      · exact hc_36 ⟨h1, h3, hc9⟩
      · by_cases h7 : 1 ≤ c7
        · exact hc_33 ⟨h1, h7, by omega⟩
        · exact hc_10 ⟨by omega, by omega⟩
    · by_cases h3 : 1 ≤ c3
      · by_cases h7 : 1 ≤ c7
        · exact hc_34 ⟨h3, h7, by omega⟩
        · exact hc_11 ⟨by omega, by omega⟩
      · exact hc_12 ⟨by omega, by omega⟩
  have hcov_false : coveredTuple c1 c3 c7 c9 = false := by
    unfold coveredTuple
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · by_contra h; push Not at h; exact hc_0 ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_1 h
    · by_contra h; push Not at h; exact hc_2 h
    · by_contra h; push Not at h; exact hc_3 h
    · by_contra h; push Not at h; exact hc_4 h
    · by_contra h; push Not at h; exact hc_5 h
    · by_contra h; push Not at h; exact hc_6 h
    · by_contra h; push Not at h; exact hc_7 h
    · by_contra h; push Not at h; exact hc_8 h
    · by_contra h; push Not at h; exact hc_9 h
    · by_contra h; push Not at h; exact hc_10 h
    · by_contra h; push Not at h; exact hc_11 h
    · by_contra h; push Not at h; exact hc_12 h
    · by_contra h; push Not at h; exact hc_13 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_14 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_15 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_16 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_17 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_18 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_19 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_20 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_21 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_22 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_23 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_24 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_25 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_26 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_27 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_28 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_29 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_30 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_31 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_32 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_33 ⟨h.1.1, h.1.2, h.2⟩
    · by_contra h; push Not at h; exact hc_34 ⟨h.1.1, h.1.2, h.2⟩
  have hfin : (c1, c3, c7, c9) ∈ exactTupleList :=
    small_tuple_exhaustive ⟨c1, by omega⟩ ⟨c3, by omega⟩ ⟨c7, by omega⟩ ⟨c9, by omega⟩
      hn1 hn3 hn7 hn9 hcov_false
  unfold exactTupleList at hfin
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hfin
  rcases hfin with ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩ | ⟨h1, h3, h7, h9⟩
  · exact ex_0_1_1_1 hperm hadm h1 h3 h7 h9
  · exact ex_1_0_1_1 hperm hadm h1 h3 h7 h9
  · exact ex_1_1_0_1 hperm hadm h1 h3 h7 h9
  · exact ex_1_1_1_0 hperm hadm h1 h3 h7 h9
  · exact ex_0_0_2_2 hperm hadm h1 h3 h7 h9
  · exact ex_0_1_1_2 hperm hadm h1 h3 h7 h9
  · exact ex_0_1_2_1 hperm hadm h1 h3 h7 h9
  · exact ex_0_2_0_2 hperm hadm h1 h3 h7 h9
  · exact ex_0_2_1_1 hperm hadm h1 h3 h7 h9
  · exact ex_0_2_2_0 hperm hadm h1 h3 h7 h9
  · exact ex_1_0_1_2 hperm hadm h1 h3 h7 h9
  · exact ex_1_0_2_1 hperm hadm h1 h3 h7 h9
  · exact ex_1_1_0_2 hperm hadm h1 h3 h7 h9
  · exact ex_1_1_2_0 hperm hadm h1 h3 h7 h9
  · exact ex_1_2_0_1 hperm hadm h1 h3 h7 h9
  · exact ex_1_2_1_0 hperm hadm h1 h3 h7 h9
  · exact ex_2_0_0_2 hperm hadm h1 h3 h7 h9
  · exact ex_2_0_1_1 hperm hadm h1 h3 h7 h9
  · exact ex_2_0_2_0 hperm hadm h1 h3 h7 h9
  · exact ex_2_1_0_1 hperm hadm h1 h3 h7 h9
  · exact ex_2_1_1_0 hperm hadm h1 h3 h7 h9
  · exact ex_2_2_0_0 hperm hadm h1 h3 h7 h9
  · exact ex_3_0_1_1 hperm hadm h1 h3 h7 h9
  · exact ex_1_1_0_3 hperm hadm h1 h3 h7 h9
  · exact ex_4_0_1_1 hperm hadm h1 h3 h7 h9
  · exact ex_1_1_0_4 hperm hadm h1 h3 h7 h9

end OMA.Proof_oeis_a003459_R1_H1

theorem OMA.solution : OMA.R_oeis_a003459_R1.H1 := by
  intro p hp hperm
  open OMA.Proof_oeis_a003459_R1_H1 in
  have hadm := digits_admissible hp hperm
  refine ⟨hadm, ?_⟩
  by_contra hno
  push Not at hno
  exact no_multi_digits hp hperm hadm (hno 1) (hno 3) (hno 7) (hno 9)
