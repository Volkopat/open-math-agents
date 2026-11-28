import OMAReductions.R_Grimm_grimm_conjecture_R1_H2_R1

namespace OMA.Proof_Grimm_grimm_conjecture_R1_H2_R1_H1

open OMA.R_Grimm_grimm_conjecture_R1_H2_R1

private def noDivUpTo (q : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | d + 1 =>
    (if (d + 1) * (d + 1) ≤ q then q % (d + 1) != 0 else true) && noDivUpTo q d

private lemma not_dvd_of_noDivUpTo {q m d : ℕ} (h : noDivUpTo q m = true)
    (hd2 : 2 ≤ d) (hdm : d ≤ m) (hsq : d * d ≤ q) : ¬ d ∣ q := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ m' =>
      unfold noDivUpTo at h
      simp only [Bool.and_eq_true] at h
      by_cases hEq : d = m' + 2
      · subst hEq
        have h1 := h.1
        rw [if_pos hsq] at h1
        simp only [bne_iff_ne, ne_eq] at h1
        intro hdvd
        exact h1 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih h.2 (by omega)

private def isPrimeCert (q : ℕ) : Bool :=
  decide (2 ≤ q) && decide (q < 168 * 168) && noDivUpTo q 167

private lemma prime_of_isPrimeCert {q : ℕ} (h : isPrimeCert q = true) : q.Prime := by
  unfold isPrimeCert at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hq2, hqhi⟩, hnd⟩ := h
  rw [Nat.prime_def_lt']
  refine ⟨hq2, fun d hd2 hdlt hdvd => ?_⟩
  by_cases hle : d * d ≤ q
  · have hd167 : d ≤ 167 := by nlinarith
    exact not_dvd_of_noDivUpTo hnd hd2 hd167 hle hdvd
  · have hqdiv : q / d ∣ q := Nat.div_dvd_of_dvd hdvd
    have hq2' : 2 ≤ q / d := by
      obtain ⟨c, hc⟩ := hdvd
      have hc2 : 2 ≤ c := by
        by_contra hlt
        have : c = 0 ∨ c = 1 := by omega
        rcases this with rfl | rfl <;> omega
      rw [hc, Nat.mul_div_cancel_left c (by omega)]
      exact hc2
    have hprod : (q / d) * d = q := Nat.div_mul_cancel hdvd
    have hlt2 : q / d < d := by nlinarith
    have hsq' : (q / d) * (q / d) ≤ q := by nlinarith
    have hq167 : q / d ≤ 167 := by nlinarith
    exact not_dvd_of_noDivUpTo hnd hq2' hq167 hsq' hqdiv

private def allDistinctAux : List ℕ → List ℕ → Bool
  | [], _ => true
  | q :: qs, seen => (!seen.contains q) && allDistinctAux qs (q :: seen)

private lemma nodup_of_allDistinctAux (l seen : List ℕ)
    (h : allDistinctAux l seen = true) :
    l.Nodup ∧ ∀ x ∈ l, x ∉ seen := by
  induction l generalizing seen with
  | nil => simp
  | cons q qs ih =>
    unfold allDistinctAux at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    have hq_not_seen : q ∉ seen := by
      intro hm
      have hc : seen.contains q = true := List.contains_iff_mem.mpr hm
      rw [h.1] at hc
      exact Bool.false_ne_true hc
    obtain ⟨hnodup, hseen⟩ := ih (q :: seen) h.2
    refine ⟨List.nodup_cons.mpr ⟨fun hq => hseen q hq (by simp), hnodup⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hq_not_seen
    · exact fun hm => hseen x hx' (List.mem_cons_of_mem q hm)

private def checkCertsAux (lo : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | j, q :: qs => isPrimeCert q && ((lo + j) % q == 0) && checkCertsAux lo (j + 1) qs

private lemma checkCertsAux_spec (lo : ℕ) (j : ℕ) (qs : List ℕ)
    (h : checkCertsAux lo j qs = true) (i : ℕ) (hi : i < qs.length) :
    (qs[i]).Prime ∧ qs[i] ∣ lo + j + i := by
  induction qs generalizing j i with
  | nil => simp at hi
  | cons q rest ih =>
    unfold checkCertsAux at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero =>
      simpa using ⟨prime_of_isPrimeCert h.1.1, Nat.dvd_of_mod_eq_zero h.1.2⟩
    | succ i' =>
      have hrec := ih (j + 1) h.2 i' (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i'] using hrec

private def checkEntry (e : ℕ × ℕ × ℕ × List ℕ) : Bool :=
  let d := e.1
  let pL := e.2.1
  let pR := e.2.2.1
  let certs := e.2.2.2
  let lo := max (pL + 1) (d - 12)
  let hi := min (pR - 1) (d + 12)
  decide (pL < d) && decide (d < pR) &&
  (decide (pL == 1) || isPrimeCert pL) &&
  isPrimeCert pR &&
  (certs.length == hi + 1 - lo) &&
  checkCertsAux lo 0 certs &&
  allDistinctAux (certs.filter (fun q => decide (q < 13))) []

private def grimmTable_0 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (4, 3, 5, [2]),
  (6, 5, 7, [2]),
  (8, 7, 11, [2,3,5]),
  (9, 7, 11, [2,3,5]),
  (10, 7, 11, [2,3,5]),
  (12, 11, 13, [2]),
  (14, 13, 17, [7,3,2]),
  (15, 13, 17, [7,3,2]),
  (18, 17, 19, [2]),
  (20, 19, 23, [2,3,11]),
  (21, 19, 23, [2,3,11]),
  (22, 19, 23, [2,3,11]),
  (24, 23, 29, [2,5,13,3,7]),
  (28, 23, 29, [2,5,13,3,7]),
  (30, 29, 31, [2]),
  (33, 31, 37, [2,11,17,5,3]),
  (35, 31, 37, [2,11,17,5,3]),
  (36, 31, 37, [2,11,17,5,3]),
  (40, 37, 41, [19,13,2]),
  (42, 41, 43, [2]),
  (44, 43, 47, [2,3,23]),
  (45, 43, 47, [2,3,23]),
  (55, 53, 59, [2,5,7,19,29]),
  (56, 53, 59, [2,5,7,19,29]),
  (60, 59, 61, [2]),
  (63, 61, 67, [31,3,2,13,11]),
  (66, 61, 67, [31,3,2,13,11]),
  (70, 67, 71, [17,23,2]),
  (72, 71, 73, [2]),
  (77, 73, 79, [37,3,19,7,13])
]
private lemma grimmTable_0_ok : grimmTable_0.all checkEntry = true := by decide

private def grimmTable_1 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (84, 83, 89, [2,17,43,29,11]),
  (88, 83, 89, [2,17,43,29,11]),
  (90, 89, 97, [2,13,23,31,47,19,3]),
  (99, 97, 101, [2,3,5]),
  (105, 103, 107, [13,3,53]),
  (110, 109, 113, [2,37,7]),
  (120, 113, 127, [19,23,29,13,59,17,2,11,61,41,31,5,3]),
  (126, 113, 127, [19,23,29,13,59,17,2,11,61,41,31,5,3]),
  (132, 131, 137, [2,19,67,3,17]),
  (140, 139, 149, [2,47,71,13,3,29,73,7,37]),
  (154, 151, 157, [19,17,2,31,13]),
  (165, 163, 167, [41,3,83]),
  (168, 167, 173, [2,13,17,19,43]),
  (180, 179, 181, [2]),
  (198, 197, 199, [2]),
  (210, 199, 211, [2,67,101,29,17,41,103,23,13,19,3]),
  (220, 211, 223, [53,71,107,43,2,31,109,73,5,13,37]),
  (231, 229, 233, [23,3,29]),
  (252, 251, 257, [3,23,127,17,2]),
  (264, 263, 269, [2,53,19,89,67]),
  (280, 277, 281, [139,31,2]),
  (308, 307, 311, [2,103,31]),
  (315, 313, 317, [157,3,79]),
  (330, 317, 331, [53,29,2,107,23,17,3,13,163,109,41,47,5]),
  (360, 359, 367, [2,19,181,3,13,73,61]),
  (385, 383, 389, [2,5,193,43,97]),
  (396, 389, 397, [13,17,2,131,197,79,3]),
  (420, 419, 421, [2]),
  (440, 439, 443, [2,3,13]),
  (462, 461, 463, [2])
]
private lemma grimmTable_1_ok : grimmTable_1.all checkEntry = true := by decide

private def grimmTable_2 : List (ℕ × ℕ × ℕ × List ℕ) := [
  (495, 491, 499, [41,17,13,3,31,71,83]),
  (504, 503, 509, [2,101,23,13,127]),
  (616, 613, 617, [307,41,2]),
  (630, 619, 631, [31,23,311,89,13,5,313,19,157,17,2]),
  (660, 659, 661, [2]),
  (693, 691, 701, [173,3,347,139,29,17,349,233,2]),
  (770, 769, 773, [2,257,193]),
  (792, 787, 797, [197,263,79,113,2,13,397,53,199]),
  (840, 839, 853, [2,29,421,281,211,13,47,7,53,283,17,23,71]),
  (924, 919, 929, [23,307,461,13,2,37,463,103,29]),
  (990, 983, 991, [41,197,17,47,13,23,2]),
  (1155, 1153, 1163, [577,3,17,13,193,19,29,43,83]),
  (1260, 1259, 1277, [2,13,631,421,79,23,211,181,317,47,127,31,53]),
  (1320, 1319, 1321, [2]),
  (1386, 1381, 1399, [691,461,173,277,2,19,347,463,139,13,29,199,17,31,349,127,233]),
  (1540, 1531, 1543, [383,73,13,307,2,29,769,19,5,23,257]),
  (1848, 1847, 1861, [2,43,37,617,463,17,103,53,29,619,929,13,31]),
  (1980, 1979, 1987, [2,283,991,661,31,397,331]),
  (2310, 2309, 2311, [2]),
  (2520, 2503, 2521, [19,13,251,31,157,359,419,503,17,839,1259,229,2]),
  (2772, 2767, 2777, [173,13,277,17,2,47,19,37,347]),
  (3080, 3079, 3083, [2,13,23]),
  (3465, 3463, 3467, [433,3,1733]),
  (3960, 3947, 3967, [47,359,79,439,13,59,659,113,23,1319,1979,37,2,17,283,1321,991,13,661]),
  (4620, 4603, 4621, [2,419,461,29,1153,659,769,13,577,19,2309,31,3]),
  (5544, 5531, 5557, [461,503,2767,41,173,113,13,29,277,1847,17,23,2,1109,47,43,19,31,37,13,347,617,2777,101,463]),
  (6930, 6917, 6947, [1153,17,173,769,3461,23,577,277,3463,2309,433,13,2,29,1733,2311,3467,19,17,991,3469,257,347,631,13]),
  (9240, 9239, 9241, [2]),
  (13860, 13859, 13873, [2,83,29,4621,1733,47,2311,283,3467,23,19,13,17]),
  (27720, 27701, 27733, [2309,229,17,3079,433,37,31,23,13,9239,13859,53,2,19,83,9241,29,1109,4621,17,1733,13,47,2521,2311])
]
private lemma grimmTable_2_ok : grimmTable_2.all checkEntry = true := by decide

private def grimmTable : List (ℕ × ℕ × ℕ × List ℕ) :=
  grimmTable_0 ++ grimmTable_1 ++ grimmTable_2

private lemma grimmTable_all_ok : grimmTable.all checkEntry = true := by
  unfold grimmTable
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨grimmTable_0_ok, grimmTable_1_ok⟩, grimmTable_2_ok⟩

private lemma dvd_27720_decomp {d : ℕ} (hd : d ∣ 27720) :
    ∃ (a : Fin 4) (b : Fin 3) (c : Fin 2) (e : Fin 2) (f : Fin 2),
      d = 2 ^ a.val * 3 ^ b.val * 5 ^ c.val * 7 ^ e.val * 11 ^ f.val := by
  have h1 : d ∣ 2 ^ 3 * (3 ^ 2 * (5 ^ 1 * (7 ^ 1 * 11 ^ 1))) := by simpa using hd
  obtain ⟨x2, r1, hx2, hr1, rfl⟩ := Nat.dvd_mul.mp h1
  obtain ⟨x3, r2, hx3, hr2, rfl⟩ := Nat.dvd_mul.mp hr1
  obtain ⟨x5, r3, hx5, hr3, rfl⟩ := Nat.dvd_mul.mp hr2
  obtain ⟨x7, x11, hx7, hx11, rfl⟩ := Nat.dvd_mul.mp hr3
  obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hx2
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hx3
  obtain ⟨c, hc, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hx5
  obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 7)).mp hx7
  obtain ⟨f, hf, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 11)).mp hx11
  exact ⟨⟨a, by omega⟩, ⟨b, by omega⟩, ⟨c, by omega⟩, ⟨e, by omega⟩, ⟨f, by omega⟩, by ring⟩

private lemma comp_div_mem_table_fin :
    ∀ (a : Fin 4) (b : Fin 3) (c : Fin 2) (e : Fin 2) (f : Fin 2),
      let d := 2 ^ a.val * 3 ^ b.val * 5 ^ c.val * 7 ^ e.val * 11 ^ f.val
      2 ≤ d → isPrimeCert d = false →
      (grimmTable.map Prod.fst).contains d = true := by
  decide

private lemma comp_div_mem_table {d : ℕ} (hd : d ∣ 27720) (h2 : 2 ≤ d)
    (hnp : isPrimeCert d = false) :
    (grimmTable.map Prod.fst).contains d = true := by
  obtain ⟨a, b, c, e, f, rfl⟩ := dvd_27720_decomp hd
  exact comp_div_mem_table_fin a b c e f h2 hnp

private lemma not_composite_of_one_or_prime {q : ℕ} (h : q = 1 ∨ q.Prime) : ¬ q.Composite := by
  intro hc
  rcases h with rfl | hp
  · exact absurd hc.1 (by omega)
  · exact hc.2 hp

private lemma lcm_Ico_dvd_27720 {k : ℕ} (hk4 : 4 ≤ k) (hk13 : k ≤ 13) :
    (Finset.Ico 1 k).lcm id ∣ 27720 := by
  interval_cases k <;> decide

private lemma filter_getElem_inj {certs : List ℕ}
    (hnodup : (certs.filter (fun q => decide (q < 13))).Nodup)
    {i j : ℕ} (hi : i < certs.length) (hj : j < certs.length)
    (hli : certs[i] < 13) (hlj : certs[j] < 13)
    (heq : certs[i] = certs[j]) : i = j := by
  -- Prove via induction on certs: wait, filter doesn't preserve index directly,
  -- so prove directly that distinct indices with < 13 produce distinct elements in filter!
  induction certs generalizing i j with
  | nil => simp at hi
  | cons q rest ih =>
    by_cases hq : q < 13
    · have hfilt : (q :: rest).filter (fun x => decide (x < 13)) =
          q :: rest.filter (fun x => decide (x < 13)) := by simp [hq]
      rw [hfilt, List.nodup_cons] at hnodup
      cases i with
      | zero =>
        cases j with
        | zero => rfl
        | succ j' =>
          exfalso
          apply hnodup.1
          rw [List.mem_filter]
          simp only [decide_eq_true_eq]
          have hj' : j' < rest.length := by simpa using hj
          have hmem : rest[j'] ∈ rest := List.getElem_mem hj'
          have heq' : q = rest[j'] := heq
          exact ⟨heq' ▸ hmem, hq⟩
      | succ i' =>
        cases j with
        | zero =>
          exfalso
          apply hnodup.1
          rw [List.mem_filter]
          simp only [decide_eq_true_eq]
          have hi' : i' < rest.length := by simpa using hi
          have hmem : rest[i'] ∈ rest := List.getElem_mem hi'
          have heq' : rest[i'] = q := heq
          exact ⟨heq' ▸ hmem, hq⟩
        | succ j' =>
          congr 1
          exact ih hnodup.2 (by simpa using hi) (by simpa using hj) (by simpa using hli) (by simpa using hlj) (by simpa using heq)
    · have hfilt : (q :: rest).filter (fun x => decide (x < 13)) =
          rest.filter (fun x => decide (x < 13)) := by simp [hq]
      rw [hfilt] at hnodup
      cases i with
      | zero => exact absurd (by simpa using hli) hq
      | succ i' =>
        cases j with
        | zero => exact absurd (by simpa using hlj) hq
        | succ j' =>
          congr 1
          exact ih hnodup (by simpa using hi) (by simpa using hj) (by simpa using hli) (by simpa using hlj) (by simpa using heq)

end OMA.Proof_Grimm_grimm_conjecture_R1_H2_R1_H1

theorem OMA.solution : OMA.R_Grimm_grimm_conjecture_R1_H2_R1.H1 := by
  intro n k hn hk4 hk13 _ hcomp T hT _
  open OMA.R_Grimm_grimm_conjecture_R1_H2_R1 OMA.Proof_Grimm_grimm_conjecture_R1_H2_R1_H1 in
  by_contra hlt
  rw [not_le] at hlt
  have hn0 : ∀ i : Fin k, n + (i : ℕ) ≠ 0 := fun i => by have := (hcomp i).1; omega
  obtain ⟨m, hmT, hsmall⟩ := exists_member_small_powers hn0 T hlt
  set d : ℕ := n + (m : ℕ)
  have hd_dvd_lcm : d ∣ (Finset.Ico 1 k).lcm id := dvd_lcm_of_small_powers (hn0 m) hsmall
  have hd_dvd : d ∣ 27720 := hd_dvd_lcm.trans (lcm_Ico_dvd_27720 hk4 hk13)
  have hd_le : d ≤ 27720 := Nat.le_of_dvd (by decide) hd_dvd
  have hd_comp : d.Composite := hcomp m
  have hd_ge2 : 2 ≤ d := hd_comp.1
  have hd_not_pcert : isPrimeCert d = false := by
    cases h : isPrimeCert d with
    | false => rfl
    | true => exact absurd (prime_of_isPrimeCert h) hd_comp.2
  have hcont := comp_div_mem_table hd_dvd hd_ge2 hd_not_pcert
  rw [List.contains_iff_exists_mem_beq] at hcont
  obtain ⟨d', hd'mem, hd'eq⟩ := hcont
  simp only [beq_iff_eq] at hd'eq
  rw [List.mem_map] at hd'mem
  obtain ⟨⟨d0, pL, pR, certs⟩, hemem, hdeq⟩ := hd'mem
  dsimp only at hdeq
  have hd0 : d0 = d := hdeq.trans hd'eq.symm
  subst hd0
  have heok : checkEntry (d, pL, pR, certs) = true :=
    List.all_eq_true.mp grimmTable_all_ok _ hemem
  unfold checkEntry at heok
  dsimp only at heok
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at heok
  obtain ⟨⟨⟨⟨⟨⟨hpL_lt, hd_lt_pR⟩, hpL_cert⟩, hpR_cert⟩, hlen⟩, hcerts⟩, hdist⟩ := heok
  have hpL_nc : ¬ pL.Composite := by
    apply not_composite_of_one_or_prime
    rcases hpL_cert with h1 | hp
    · exact Or.inl h1
    · exact Or.inr (prime_of_isPrimeCert hp)
  have hpR_nc : ¬ pR.Composite := not_composite_of_one_or_prime (Or.inr (prime_of_isPrimeCert hpR_cert))
  have hpL_lt_n : pL < n := by
    by_contra hle
    have hidx : pL - n < k := by omega
    have hc := hcomp ⟨pL - n, hidx⟩
    have heq : n + (pL - n) = pL := by omega
    rw [heq] at hc
    exact hpL_nc hc
  have hnk_le_pR : n + k ≤ pR := by
    by_contra hgt
    have hidx : pR - n < k := by omega
    have hc := hcomp ⟨pR - n, hidx⟩
    have heq : n + (pR - n) = pR := by omega
    rw [heq] at hc
    exact hpR_nc hc
  let lo : ℕ := max (pL + 1) (d - 12)
  let hi : ℕ := min (pR - 1) (d + 12)
  have hbounds : ∀ i : Fin k, lo ≤ n + (i : ℕ) ∧ n + (i : ℕ) ≤ hi := by
    intro i
    have him : (m : ℕ) < k := m.isLt
    have hi' : (i : ℕ) < k := i.isLt
    dsimp only [lo, hi]
    omega
  have hidx_lt : ∀ i : Fin k, n + (i : ℕ) - lo < certs.length := by
    intro i
    have hb := hbounds i
    omega
  have hnodup : (certs.filter (fun q => decide (q < 13))).Nodup :=
    (nodup_of_allDistinctAux _ [] hdist).1
  let f : Fin k → ℕ := fun i => certs[n + (i : ℕ) - lo]'(hidx_lt i)
  have hf_mem : ∀ i ∈ T, f i ∈ T.biUnion (fun j => (n + (j : ℕ)).primeFactors) := by
    intro i hiT
    have hspec := checkCertsAux_spec lo 0 certs hcerts (n + (i : ℕ) - lo) (hidx_lt i)
    have hb := hbounds i
    have hadd : lo + 0 + (n + (i : ℕ) - lo) = n + (i : ℕ) := by omega
    rw [hadd] at hspec
    exact Finset.mem_biUnion.mpr ⟨i, hiT, Nat.mem_primeFactors.mpr ⟨hspec.1, hspec.2, hn0 i⟩⟩
  have hf_lt13 : ∀ i ∈ T, f i < 13 := by
    intro i hiT
    have hspec := checkCertsAux_spec lo 0 certs hcerts (n + (i : ℕ) - lo) (hidx_lt i)
    have hb := hbounds i
    have hadd : lo + 0 + (n + (i : ℕ) - lo) = n + (i : ℕ) := by omega
    rw [hadd] at hspec
    have hlt_k := hT i hiT (f i) hspec.1 hspec.2
    omega
  have hf_inj : Set.InjOn f ↑T := by
    intro i hiT j hjT heq
    have hidx_eq := filter_getElem_inj hnodup (hidx_lt i) (hidx_lt j)
      (hf_lt13 i hiT) (hf_lt13 j hjT) heq
    have hbi := hbounds i
    have hbj := hbounds j
    exact Fin.ext (by omega)
  have hcard := Finset.card_le_card_of_injOn f hf_mem hf_inj
  omega
