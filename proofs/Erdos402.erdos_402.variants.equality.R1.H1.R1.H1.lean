import OMAReductions.R_Erdos402_erdos_402_variants_equality_R1_H1_R1

/-!
# Finite prime corridors for Graham's equality conjecture

Balasubramanian and Soundararajan, Acta Arithmetica 75 (1996), 1–38, Lemma 3.3
and the two exceptional cases following it. The square-gap bound handles 419
intervals, each with two prime witnesses that work throughout the interval.
The remaining 52 singleton intervals use trial division and divisor counts.
-/

namespace OMA.Erdos402Window

/-- Upper bound on the size of a cluster of divisors of b whose largest-to-smallest
ratio is at most n/b. -/
private def clusterBound (n b : ℕ) : ℕ :=
  b.divisors.sup fun x =>
    (b.divisors.filter (fun y => x ≤ y ∧ b * y ≤ n * x)).card

private def primeSlots (n p : ℕ) : Finset ℕ :=
  (Finset.Icc (max (p - n) (n / 2 + 1)) n).filter Nat.Prime

private def fastDivisors (b : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 b.sqrt).filter (· ∣ b)).biUnion fun d => {d, b / d}

private theorem fastDivisors_eq (b : ℕ) : fastDivisors b = b.divisors := by
  classical
  by_cases hb : b = 0
  · subst b
    simp [fastDivisors]
  have hb0 := Nat.pos_of_ne_zero hb
  ext a
  constructor
  · intro h
    obtain ⟨d, hd, ha⟩ := Finset.mem_biUnion.mp h
    have hdiv := (Finset.mem_filter.mp hd).2
    have hm : a = d ∨ a = b / d := by simpa using ha
    apply Nat.mem_divisors.mpr
    rcases hm with rfl | rfl
    · exact ⟨hdiv, hb⟩
    · exact ⟨Nat.div_dvd_of_dvd hdiv, hb⟩
  · intro ha
    have had := (Nat.mem_divisors.mp ha).1
    have hap := Nat.pos_of_dvd_of_pos had hb0
    have he := Nat.div_mul_cancel had
    rcases Nat.le_sqrt_of_eq_mul he.symm with hq | hs
    · refine Finset.mem_biUnion.mpr ⟨b / a, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hb0 had) hap, hq⟩
      · exact Nat.div_dvd_of_dvd had
      · have hinv := Nat.div_div_self had hb
        simp [hinv]
    · refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨?_, had⟩, by simp⟩
      exact Finset.mem_Icc.mpr ⟨hap, hs⟩

private theorem close_distinct_divisors {n b x y : ℕ} (hb : 0 < b) (hbn : b ≤ n)
    (hx : x ∣ b) (hy : y ∣ b) (hxy : x < y) (hclose : b * y ≤ n * x) :
    n ≤ (n - b) ^ 2 := by
  have hx0 := Nat.pos_of_dvd_of_pos hx hb
  let g := x.gcd y
  let u := x / g
  let v := y / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left y hx0
  have hu : u * g = x := Nat.div_mul_cancel (Nat.gcd_dvd_left x y)
  have hv : v * g = y := Nat.div_mul_cancel (Nat.gcd_dvd_right x y)
  have hcop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  have hub : u ∣ b := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left x y)).trans hx
  have hvb : v ∣ b := (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right x y)).trans hy
  have hscale : u * g < v * g := by
    simpa only [hu, hv] using hxy
  have huv : u < v := Nat.lt_of_mul_lt_mul_right hscale
  have hmul : u * v ≤ b := Nat.le_of_dvd hb (hcop.mul_dvd_of_dvd_of_dvd hub hvb)
  have hratio : b * v ≤ n * u := by
    apply Nat.le_of_mul_le_mul_right _ hg
    simpa only [mul_assoc, hu, hv] using hclose
  have hbMul : b * (u + 1) ≤ n * u :=
    (Nat.mul_le_mul_left b (Nat.succ_le_of_lt huv)).trans hratio
  have hnm : n * u = b * u + (n - b) * u := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hbn]
  have hbBound : b ≤ (n - b) * u := by
    rw [Nat.mul_succ, hnm] at hbMul
    exact Nat.le_of_add_le_add_left hbMul
  have hnTimes : n * (u + 1) ≤ n * v :=
    Nat.mul_le_mul_left n (Nat.succ_le_of_lt huv)
  have hnv : n * v = b * v + (n - b) * v := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hbn]
  have hnBound : n ≤ (n - b) * v := by
    rw [Nat.mul_succ] at hnTimes
    have h := (Nat.add_le_add_right hratio n).trans hnTimes
    rw [hnv] at h
    exact Nat.le_of_add_le_add_left h
  have hs : b * n ≤ (n - b)^2 * b := by
    calc
      b * n ≤ ((n - b) * u) * ((n - b) * v) := Nat.mul_le_mul hbBound hnBound
      _ = (n - b)^2 * (u * v) := by ring
      _ ≤ (n - b)^2 * b := Nat.mul_le_mul_left _ hmul
  exact Nat.le_of_mul_le_mul_right (by simpa only [Nat.mul_comm b n] using hs) hb

theorem clusterBound_eq_one_of_sq_lt {n b : ℕ} (hb : 0 < b) (hbn : b ≤ n)
    (hfar : (n - b)^2 < n) : clusterBound n b = 1 := by
  apply le_antisymm
  · unfold clusterBound
    apply Finset.sup_le
    intro x hx
    have hsub :
        (b.divisors.filter (fun y => x ≤ y ∧ b * y ≤ n * x)) ⊆ ({x} : Finset ℕ) := by
      intro y hy
      obtain ⟨hy, hxy, hclose⟩ := Finset.mem_filter.mp hy
      have he : x = y := by
        by_contra! hne
        exact hfar.not_ge (close_distinct_divisors hb hbn (Nat.mem_divisors.mp hx).1
          (Nat.mem_divisors.mp hy).1 (lt_of_le_of_ne hxy hne) hclose)
      simp [he]
    simpa using Finset.card_le_card hsub
  · unfold clusterBound
    apply Finset.le_sup_of_le (Nat.mem_divisors.mpr ⟨one_dvd b, hb.ne'⟩ : 1 ∈ b.divisors)
    apply Finset.card_pos.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd b, hb.ne'⟩, ?_⟩⟩
    simpa using hbn

private def WindowCertificate (n p : ℕ) : Prop :=
  p.Prime ∧ n < p ∧ p < 2*n ∧
    (∀ a ∈ Finset.Icc ((p+1)/2) n, n*n < 2*a*a ∧ clusterBound n a = 1) ∧
    (∑ b ∈ Finset.Icc (p-n) ((p-1)/2), (clusterBound n b - 1)) < (primeSlots n p).card

private def checkPrime (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range' 2 (p.sqrt-1)).all (fun d => decide (p % d ≠ 0))

private theorem checkPrime_iff {p : ℕ} : checkPrime p = true ↔ p.Prime := by
  rw [checkPrime, Nat.prime_def_le_sqrt, Bool.and_eq_true_iff, decide_eq_true_eq,
    List.all_eq_true]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · intro h d hd hdp
    have hm : d ∈ List.range' 2 (p.sqrt-1) := List.mem_range'_1.mpr ⟨hd, by omega⟩
    exact fun hdvd => (of_decide_eq_true (h d hm)) (Nat.dvd_iff_mod_eq_zero.mp hdvd)
  · intro h d hd
    obtain ⟨hlo, hhi⟩ := List.mem_range'_1.mp hd
    apply decide_eq_true
    exact fun hz => h d hlo (by omega) (Nat.dvd_iff_mod_eq_zero.mpr hz)

private def divisorList (b : ℕ) : List ℕ :=
  (((List.range' 1 b.sqrt).filter (fun d => decide (d ∣ b))).flatMap
    (fun d => [d, b/d])).dedup

private theorem divisorList_eq (b : ℕ) : (divisorList b).toFinset = b.divisors := by
  rw [← fastDivisors_eq]
  ext a
  simp only [List.mem_toFinset, divisorList, List.mem_dedup, List.mem_flatMap, List.mem_filter,
    decide_eq_true_eq, List.mem_range'_1, List.mem_cons, List.not_mem_nil, or_false,
    fastDivisors, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_insert, Finset.mem_singleton]
  constructor <;> rintro ⟨d, ⟨⟨h₁, h₂⟩, hd⟩, ha⟩ <;>
    exact ⟨d, ⟨⟨h₁, by omega⟩, hd⟩, ha⟩

private def listCluster (n b : ℕ) : ℕ :=
  if 0 < b ∧ b ≤ n ∧ (n-b)^2 < n then 1
  else
    let ds := divisorList b
    ds.foldr (fun x best => max (ds.countP fun y => decide (x ≤ y ∧ b*y ≤ n*x)) best) 0

private theorem listFold_eq_sup (l : List ℕ) (f : ℕ → ℕ) :
    l.foldr (fun x acc => max (f x) acc) 0 = l.toFinset.sup f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldr_cons, List.toFinset_cons, Finset.sup_insert]
    exact congrArg (max (f x)) ih

private theorem listCluster_eq (n b : ℕ) : listCluster n b = clusterBound n b := by
  unfold listCluster
  split <;> rename_i h
  · exact (clusterBound_eq_one_of_sq_lt h.1 h.2.1 h.2.2).symm
  · rw [listFold_eq_sup, divisorList_eq]
    apply congrArg (b.divisors.sup ·)
    funext x
    have hn : (divisorList b).Nodup := List.nodup_dedup _
    have hc := hn.card_eq_countP (P := fun y : ℕ => x ≤ y ∧ b*y ≤ n*x)
    rw [divisorList_eq] at hc
    exact hc.symm

private def interval (a b : ℕ) : List ℕ := List.range' a (b+1-a)

private theorem interval_toFinset (a b : ℕ) : (interval a b).toFinset = Finset.Icc a b := by
  ext x
  simp only [interval, List.mem_toFinset, List.mem_range'_1, Finset.mem_Icc]
  omega

private theorem interval_nodup (a b : ℕ) : (interval a b).Nodup := List.nodup_range'

private def checkWindow (n p : ℕ) : Bool :=
  checkPrime p && decide (n < p ∧ p < 2*n) &&
    ((interval ((p+1)/2) n).all fun a => decide (n*n < 2*a*a ∧ listCluster n a = 1)) &&
    decide ((((interval (p-n) ((p-1)/2)).map (fun b => listCluster n b - 1)).sum) <
      (interval (max (p-n) (n/2+1)) n).countP checkPrime)

private theorem checkWindow_sound {n p : ℕ} (h : checkWindow n p = true) :
    WindowCertificate n p := by
  unfold checkWindow at h
  obtain ⟨hout, hscore⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hbase, halpha⟩ := Bool.and_eq_true_iff.mp hout
  obtain ⟨hp, hlim⟩ := Bool.and_eq_true_iff.mp hbase
  obtain ⟨hlo, hhi⟩ := of_decide_eq_true hlim
  refine ⟨checkPrime_iff.mp hp, hlo, hhi, ?_, ?_⟩
  · intro a ha
    have hmem : a ∈ interval ((p+1)/2) n := by
      rw [← interval_toFinset] at ha
      exact List.mem_toFinset.mp ha
    have hentry : decide (n*n < 2*a*a ∧ listCluster n a = 1) = true :=
      List.all_eq_true.mp halpha a hmem
    simpa only [listCluster_eq] using of_decide_eq_true hentry
  · have hs := of_decide_eq_true hscore
    rw [← List.sum_toFinset _ (interval_nodup _ _), interval_toFinset] at hs
    have hcount (a b : ℕ) : (interval a b).countP checkPrime = ((Finset.Icc a b).filter Nat.Prime).card := by
      rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((interval_nodup a b).filter checkPrime),
        List.toFinset_filter, interval_toFinset]
      congr 1
      ext x
      simp only [Finset.mem_filter, checkPrime_iff]
    simpa only [listCluster_eq, hcount, primeSlots] using hs
/-- When the square of the gap is less than n, every slot allows only one
divisor. A single prime in the complementary interval certifies the window. -/
theorem simple_window {n p q : ℕ}
    (hp : p.Prime) (hnp : n < p) (hpn : p < 2*n) (hgap : (2*n-p)^2 < n)
    (hα : n*n < 2*((p+1)/2)*((p+1)/2)) (hq : q.Prime)
    (hqlo : max (p-n) (n/2+1) ≤ q) (hqhi : q ≤ n) :
    WindowCertificate n p := by
  have one (b : ℕ) (hlo : p-n ≤ b) (hhi : b ≤ n) : clusterBound n b = 1 := by
    have hd : n-b ≤ 2*n-p := by omega
    exact clusterBound_eq_one_of_sq_lt (by omega) hhi
      ((Nat.pow_le_pow_left hd 2).trans_lt hgap)
  refine ⟨hp, hnp, hpn, ?_, ?_⟩
  · intro a ha
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp ha
    exact ⟨hα.trans_le (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hlo) hlo), one a (by omega) hhi⟩
  · have hz : (∑ b ∈ Finset.Icc (p-n) ((p-1)/2), (clusterBound n b-1)) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hb
      simp only [one b hlo (by omega), Nat.sub_self]
    rw [hz]
    exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hqlo, hqhi⟩, hq⟩⟩

private def checkSpan (lo hi p q : ℕ) : Bool :=
  checkPrime p && checkPrime q &&
    decide (hi < p ∧ p < 2*lo ∧ (2*hi-p)^2 < lo ∧
    hi*hi < 2*((p+1)/2)*((p+1)/2) ∧
    max (p-lo) (hi/2+1) ≤ q ∧ q ≤ lo)

private theorem checkSpan_sound {lo hi p q n : ℕ} (h : checkSpan lo hi p q = true)
    (hlo : lo ≤ n) (hhi : n ≤ hi) : WindowCertificate n p := by
  obtain ⟨hPq, hnum⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hp, hq⟩ := Bool.and_eq_true_iff.mp hPq
  obtain ⟨hp₁, hp₂, hg, ha, hq₁, hq₂⟩ := of_decide_eq_true hnum
  refine simple_window (checkPrime_iff.mp hp) (hhi.trans_lt hp₁) (hp₂.trans_le (Nat.mul_le_mul_left _ hlo))
    ?_ ((Nat.mul_le_mul hhi hhi).trans_lt ha) (checkPrime_iff.mp hq) ?_ (hq₂.trans hlo)
  · exact (Nat.pow_le_pow_left (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hhi) _) 2).trans_lt
      (hg.trans_le hlo)
  · omega

private def checkSpans (lo hi : ℕ) : List (ℕ × ℕ × ℕ) → Bool
  | [] => decide (lo = hi+1)
  | (endAt, p, q) :: rest =>
    decide (lo ≤ endAt ∧ endAt ≤ hi) &&
      (if q = 0 then decide (lo = endAt) && checkWindow lo p else checkSpan lo endAt p q) &&
      checkSpans (endAt+1) hi rest

private theorem checkSpans_sound {lo hi n : ℕ} {entries : List (ℕ × ℕ × ℕ)}
    (h : checkSpans lo hi entries = true) (hlo : lo ≤ n) (hhi : n ≤ hi) :
    ∃ p : ℕ, WindowCertificate n p := by
  induction entries generalizing lo with
  | nil =>
    have he : lo = hi+1 := of_decide_eq_true h
    omega
  | cons entry rest ih =>
    obtain ⟨m, p, q⟩ := entry
    simp only [checkSpans, Bool.and_eq_true_iff] at h
    by_cases hm : n ≤ m
    · refine ⟨p, ?_⟩
      by_cases hq : q = 0
      · rw [if_pos hq, Bool.and_eq_true_iff] at h
        have he : lo = m := of_decide_eq_true h.1.2.1
        have hn : n = lo := by omega
        exact hn ▸ checkWindow_sound h.1.2.2
      · rw [if_neg hq] at h
        exact checkSpan_sound h.1.2 hlo hm
    · exact ih h.2 (by omega)

set_option maxRecDepth 4096 in
private def chunk0 : {L : List (ℕ × ℕ × ℕ) // checkSpans 10 23 L = true} :=
  ⟨[
    (10, 17, 7),
    (11, 19, 11),
    (13, 23, 11),
    (14, 23, 0),
    (15, 23, 0),
    (16, 29, 13),
    (17, 31, 17),
    (18, 31, 0),
    (20, 37, 19),
    (21, 37, 0),
    (22, 41, 19),
    (23, 43, 23)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk1 : {L : List (ℕ × ℕ × ℕ) // checkSpans 24 40 L = true} :=
  ⟨[
    (25, 47, 23),
    (26, 47, 23),
    (27, 43, 0),
    (28, 47, 0),
    (29, 53, 29),
    (32, 59, 29),
    (33, 61, 31),
    (34, 61, 0),
    (35, 61, 0),
    (36, 67, 31),
    (39, 73, 37),
    (40, 73, 0)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk2 : {L : List (ℕ × ℕ × ℕ) // checkSpans 41 62 L = true} :=
  ⟨[
    (42, 79, 41),
    (44, 83, 43),
    (45, 83, 0),
    (47, 89, 43),
    (48, 89, 0),
    (49, 89, 0),
    (52, 97, 47),
    (55, 103, 53),
    (58, 109, 53),
    (60, 113, 59),
    (61, 113, 0),
    (62, 113, 0)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk3 : {L : List (ℕ × ℕ × ℕ) // checkSpans 63 86 L = true} :=
  ⟨[
    (63, 113, 0),
    (64, 113, 0),
    (65, 113, 0),
    (67, 127, 61),
    (69, 131, 67),
    (72, 137, 67),
    (73, 139, 73),
    (74, 139, 0),
    (75, 139, 0),
    (78, 149, 73),
    (82, 157, 79),
    (86, 163, 83)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk4 : {L : List (ℕ × ℕ × ℕ) // checkSpans 87 116 L = true} :=
  ⟨[
    (88, 167, 83),
    (91, 173, 89),
    (95, 181, 89),
    (96, 181, 0),
    (101, 193, 97),
    (104, 199, 101),
    (105, 199, 0),
    (106, 199, 0),
    (110, 211, 107),
    (111, 211, 0),
    (112, 211, 0),
    (116, 223, 113)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk5 : {L : List (ℕ × ℕ × ℕ) // checkSpans 117 147 L = true} :=
  ⟨[
    (119, 229, 113),
    (121, 233, 113),
    (122, 233, 113),
    (123, 229, 0),
    (124, 233, 0),
    (125, 233, 0),
    (126, 239, 0),
    (131, 251, 127),
    (137, 263, 131),
    (141, 271, 137),
    (146, 281, 139),
    (147, 283, 139)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk6 : {L : List (ℕ × ℕ × ℕ) // checkSpans 148 181 L = true} :=
  ⟨[
    (148, 283, 0),
    (152, 293, 149),
    (153, 293, 0),
    (154, 293, 0),
    (155, 293, 0),
    (159, 307, 151),
    (164, 317, 157),
    (165, 317, 0),
    (166, 317, 0),
    (171, 331, 167),
    (175, 337, 167),
    (181, 349, 173)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk7 : {L : List (ℕ × ℕ × ℕ) // checkSpans 182 222 L = true} :=
  ⟨[
    (186, 359, 181),
    (190, 367, 181),
    (196, 379, 191),
    (201, 389, 197),
    (207, 401, 199),
    (208, 401, 0),
    (209, 401, 0),
    (211, 409, 199),
    (217, 421, 211),
    (218, 421, 0),
    (219, 421, 0),
    (222, 431, 211)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk8 : {L : List (ℕ × ℕ × ℕ) // checkSpans 223 289 L = true} :=
  ⟨[
    (228, 443, 223),
    (236, 457, 229),
    (241, 467, 233),
    (247, 479, 241),
    (251, 487, 241),
    (259, 503, 251),
    (262, 509, 257),
    (269, 523, 263),
    (270, 523, 0),
    (278, 541, 271),
    (281, 547, 277),
    (289, 563, 281)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk9 : {L : List (ℕ × ℕ × ℕ) // checkSpans 290 354 L = true} :=
  ⟨[
    (294, 571, 283),
    (302, 587, 293),
    (305, 593, 293),
    (308, 599, 293),
    (315, 613, 307),
    (318, 619, 313),
    (324, 631, 317),
    (329, 641, 317),
    (332, 647, 317),
    (339, 661, 331),
    (347, 677, 337),
    (354, 691, 347)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk10 : {L : List (ℕ × ℕ × ℕ) // checkSpans 355 430 L = true} :=
  ⟨[
    (359, 701, 353),
    (368, 719, 359),
    (376, 733, 367),
    (381, 743, 373),
    (390, 761, 379),
    (396, 773, 389),
    (403, 787, 397),
    (408, 797, 401),
    (415, 811, 409),
    (421, 823, 409),
    (429, 839, 421),
    (430, 839, 0)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk11 : {L : List (ℕ × ℕ × ℕ) // checkSpans 431 509 L = true} :=
  ⟨[
    (439, 859, 431),
    (448, 877, 439),
    (454, 887, 449),
    (455, 887, 0),
    (456, 887, 0),
    (466, 911, 457),
    (475, 929, 467),
    (481, 941, 467),
    (487, 953, 479),
    (496, 971, 487),
    (502, 983, 491),
    (509, 997, 503)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk12 : {L : List (ℕ × ℕ × ℕ) // checkSpans 510 612 L = true} :=
  ⟨[
    (520, 1019, 509),
    (530, 1039, 521),
    (537, 1051, 523),
    (542, 1061, 523),
    (546, 1069, 541),
    (558, 1093, 547),
    (566, 1109, 557),
    (576, 1129, 563),
    (588, 1153, 577),
    (597, 1171, 587),
    (605, 1187, 593),
    (612, 1201, 601)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk13 : {L : List (ℕ × ℕ × ℕ) // checkSpans 613 682 L = true} :=
  ⟨[
    (623, 1223, 613),
    (630, 1237, 619),
    (642, 1259, 631),
    (654, 1283, 643),
    (666, 1307, 653),
    (676, 1327, 661),
    (677, 1327, 0),
    (678, 1327, 0),
    (679, 1327, 0),
    (680, 1327, 0),
    (681, 1327, 0),
    (682, 1327, 0)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk14 : {L : List (ℕ × ℕ × ℕ) // checkSpans 683 799 L = true} :=
  ⟨[
    (693, 1361, 683),
    (703, 1381, 691),
    (712, 1399, 701),
    (717, 1409, 709),
    (726, 1427, 709),
    (739, 1453, 727),
    (749, 1471, 739),
    (760, 1493, 743),
    (769, 1511, 761),
    (779, 1531, 769),
    (790, 1553, 773),
    (799, 1571, 787)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk15 : {L : List (ℕ × ℕ × ℕ) // checkSpans 800 903 L = true} :=
  ⟨[
    (812, 1597, 797),
    (824, 1621, 811),
    (832, 1637, 823),
    (842, 1657, 829),
    (849, 1669, 839),
    (850, 1669, 0),
    (851, 1669, 0),
    (852, 1669, 0),
    (864, 1699, 853),
    (876, 1723, 863),
    (891, 1753, 877),
    (903, 1777, 887)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk16 : {L : List (ℕ × ℕ × ℕ) // checkSpans 904 1030 L = true} :=
  ⟨[
    (909, 1789, 887),
    (920, 1811, 907),
    (930, 1831, 919),
    (938, 1847, 929),
    (951, 1873, 937),
    (959, 1889, 947),
    (971, 1913, 953),
    (982, 1933, 971),
    (991, 1951, 983),
    (1005, 1979, 991),
    (1017, 2003, 997),
    (1030, 2029, 1013)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk17 : {L : List (ℕ × ℕ × ℕ) // checkSpans 1031 1165 L = true} :=
  ⟨[
    (1042, 2053, 1031),
    (1056, 2081, 1039),
    (1065, 2099, 1051),
    (1080, 2129, 1063),
    (1087, 2143, 1069),
    (1096, 2161, 1087),
    (1106, 2179, 1097),
    (1120, 2207, 1103),
    (1135, 2237, 1117),
    (1142, 2251, 1129),
    (1151, 2269, 1129),
    (1165, 2297, 1151)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk18 : {L : List (ℕ × ℕ × ℕ) // checkSpans 1166 1328 L = true} :=
  ⟨[
    (1172, 2311, 1163),
    (1187, 2341, 1171),
    (1202, 2371, 1187),
    (1216, 2399, 1201),
    (1228, 2423, 1217),
    (1241, 2447, 1229),
    (1256, 2477, 1237),
    (1269, 2503, 1249),
    (1278, 2521, 1259),
    (1296, 2557, 1279),
    (1314, 2593, 1297),
    (1328, 2621, 1307)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk19 : {L : List (ℕ × ℕ × ℕ) // checkSpans 1329 1462 L = true} :=
  ⟨[
    (1341, 2647, 1327),
    (1349, 2663, 1327),
    (1356, 2677, 1327),
    (1359, 2683, 1327),
    (1361, 2687, 1327),
    (1377, 2719, 1361),
    (1393, 2749, 1373),
    (1402, 2767, 1381),
    (1419, 2801, 1399),
    (1428, 2819, 1409),
    (1447, 2857, 1429),
    (1462, 2887, 1447)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk20 : {L : List (ℕ × ℕ × ℕ) // checkSpans 1463 1634 L = true} :=
  ⟨[
    (1477, 2917, 1459),
    (1488, 2939, 1471),
    (1504, 2971, 1489),
    (1519, 3001, 1499),
    (1530, 3023, 1511),
    (1550, 3061, 1531),
    (1564, 3089, 1549),
    (1580, 3121, 1559),
    (1588, 3137, 1579),
    (1604, 3169, 1583),
    (1621, 3203, 1601),
    (1634, 3229, 1621)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk21 : {L : List (ℕ × ℕ × ℕ) // checkSpans 1635 1785 L = true} :=
  ⟨[
    (1649, 3259, 1627),
    (1655, 3271, 1637),
    (1656, 3271, 0),
    (1676, 3313, 1657),
    (1691, 3343, 1669),
    (1701, 3361, 1669),
    (1716, 3391, 1699),
    (1727, 3413, 1709),
    (1745, 3449, 1723),
    (1755, 3469, 1741),
    (1770, 3499, 1753),
    (1785, 3529, 1759)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk22 : {L : List (ℕ × ℕ × ℕ) // checkSpans 1786 1980 L = true} :=
  ⟨[
    (1800, 3559, 1783),
    (1817, 3593, 1801),
    (1832, 3623, 1811),
    (1850, 3659, 1831),
    (1870, 3697, 1847),
    (1891, 3739, 1871),
    (1911, 3779, 1889),
    (1923, 3803, 1907),
    (1938, 3833, 1913),
    (1953, 3863, 1933),
    (1966, 3889, 1951),
    (1980, 3917, 1951)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk23 : {L : List (ℕ × ℕ × ℕ) // checkSpans 1981 2204 L = true} :=
  ⟨[
    (1995, 3947, 1979),
    (2016, 3989, 1993),
    (2035, 4027, 2017),
    (2051, 4057, 2029),
    (2068, 4091, 2039),
    (2089, 4133, 2069),
    (2111, 4177, 2089),
    (2132, 4219, 2111),
    (2153, 4261, 2131),
    (2171, 4297, 2153),
    (2186, 4327, 2161),
    (2204, 4363, 2179)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk24 : {L : List (ℕ × ℕ × ℕ) // checkSpans 2205 2425 L = true} :=
  ⟨[
    (2221, 4397, 2203),
    (2244, 4441, 2221),
    (2265, 4483, 2243),
    (2282, 4517, 2251),
    (2304, 4561, 2281),
    (2322, 4597, 2297),
    (2334, 4621, 2311),
    (2355, 4663, 2333),
    (2375, 4703, 2351),
    (2390, 4733, 2371),
    (2403, 4759, 2389),
    (2425, 4801, 2399)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk25 : {L : List (ℕ × ℕ × ℕ) // checkSpans 2426 2662 L = true} :=
  ⟨[
    (2440, 4831, 2423),
    (2463, 4877, 2441),
    (2484, 4919, 2459),
    (2503, 4957, 2477),
    (2526, 5003, 2503),
    (2544, 5039, 2521),
    (2568, 5087, 2543),
    (2584, 5119, 2557),
    (2601, 5153, 2579),
    (2620, 5189, 2593),
    (2644, 5237, 2621),
    (2662, 5273, 2633)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk26 : {L : List (ℕ × ℕ × ℕ) // checkSpans 2663 2901 L = true} :=
  ⟨[
    (2687, 5323, 2663),
    (2701, 5351, 2687),
    (2725, 5399, 2699),
    (2747, 5443, 2719),
    (2767, 5483, 2741),
    (2791, 5531, 2767),
    (2816, 5581, 2791),
    (2822, 5591, 2803),
    (2847, 5641, 2819),
    (2871, 5689, 2843),
    (2885, 5717, 2861),
    (2901, 5749, 2879)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk27 : {L : List (ℕ × ℕ × ℕ) // checkSpans 2902 3163 L = true} :=
  ⟨[
    (2922, 5791, 2897),
    (2946, 5839, 2917),
    (2967, 5881, 2939),
    (2990, 5927, 2963),
    (3003, 5953, 2971),
    (3020, 5987, 3001),
    (3045, 6037, 3019),
    (3067, 6079, 3041),
    (3094, 6133, 3067),
    (3114, 6173, 3089),
    (3138, 6221, 3109),
    (3163, 6271, 3137)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk28 : {L : List (ℕ × ℕ × ℕ) // checkSpans 3164 3430 L = true} :=
  ⟨[
    (3189, 6323, 3163),
    (3214, 6373, 3187),
    (3238, 6421, 3209),
    (3253, 6451, 3229),
    (3274, 6491, 3253),
    (3293, 6529, 3271),
    (3310, 6563, 3271),
    (3332, 6607, 3307),
    (3359, 6661, 3331),
    (3388, 6719, 3359),
    (3410, 6763, 3389),
    (3430, 6803, 3407)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk29 : {L : List (ℕ × ℕ × ℕ) // checkSpans 3431 3726 L = true} :=
  ⟨[
    (3449, 6841, 3413),
    (3478, 6899, 3449),
    (3502, 6947, 3469),
    (3530, 7001, 3499),
    (3558, 7057, 3529),
    (3584, 7109, 3559),
    (3609, 7159, 3583),
    (3636, 7213, 3607),
    (3656, 7253, 3637),
    (3678, 7297, 3643),
    (3705, 7351, 3677),
    (3726, 7393, 3701)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk30 : {L : List (ℕ × ℕ × ℕ) // checkSpans 3727 4037 L = true} :=
  ⟨[
    (3756, 7451, 3727),
    (3775, 7489, 3739),
    (3801, 7541, 3769),
    (3826, 7591, 3797),
    (3855, 7649, 3823),
    (3882, 7703, 3853),
    (3910, 7759, 3881),
    (3939, 7817, 3911),
    (3964, 7867, 3931),
    (3984, 7907, 3947),
    (4007, 7951, 3967),
    (4037, 8011, 4007)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk31 : {L : List (ℕ × ℕ × ℕ) // checkSpans 4038 4337 L = true} :=
  ⟨[
    (4061, 8059, 4027),
    (4090, 8117, 4057),
    (4121, 8179, 4091),
    (4148, 8233, 4111),
    (4175, 8287, 4139),
    (4196, 8329, 4159),
    (4216, 8369, 4177),
    (4247, 8431, 4217),
    (4266, 8467, 4243),
    (4296, 8527, 4261),
    (4323, 8581, 4297),
    (4337, 8609, 4297)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk32 : {L : List (ℕ × ℕ × ℕ) // checkSpans 4338 4662 L = true} :=
  ⟨[
    (4367, 8669, 4337),
    (4398, 8731, 4363),
    (4424, 8783, 4397),
    (4452, 8839, 4423),
    (4479, 8893, 4451),
    (4503, 8941, 4463),
    (4519, 8971, 4493),
    (4548, 9029, 4519),
    (4579, 9091, 4549),
    (4602, 9137, 4567),
    (4635, 9203, 4603),
    (4662, 9257, 4621)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk33 : {L : List (ℕ × ℕ × ℕ) // checkSpans 4663 5009 L = true} :=
  ⟨[
    (4695, 9323, 4663),
    (4722, 9377, 4691),
    (4753, 9439, 4723),
    (4782, 9497, 4751),
    (4810, 9551, 4783),
    (4835, 9601, 4801),
    (4865, 9661, 4831),
    (4895, 9721, 4861),
    (4925, 9781, 4889),
    (4954, 9839, 4919),
    (4985, 9901, 4951),
    (5009, 9949, 4973)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk34 : {L : List (ℕ × ℕ × ℕ) // checkSpans 5010 5370 L = true} :=
  ⟨[
    (5039, 10009, 5009),
    (5074, 10079, 5039),
    (5102, 10133, 5059),
    (5132, 10193, 5101),
    (5159, 10247, 5119),
    (5192, 10313, 5153),
    (5220, 10369, 5189),
    (5250, 10429, 5209),
    (5279, 10487, 5237),
    (5315, 10559, 5279),
    (5342, 10613, 5309),
    (5370, 10667, 5333)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk35 : {L : List (ℕ × ℕ × ℕ) // checkSpans 5371 5729 L = true} :=
  ⟨[
    (5392, 10711, 5351),
    (5427, 10781, 5393),
    (5460, 10847, 5419),
    (5491, 10909, 5449),
    (5523, 10973, 5483),
    (5550, 11027, 5521),
    (5572, 11071, 5531),
    (5602, 11131, 5573),
    (5625, 11177, 5591),
    (5659, 11243, 5623),
    (5696, 11317, 5659),
    (5729, 11383, 5693)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk36 : {L : List (ℕ × ℕ × ℕ) // checkSpans 5730 6095 L = true} :=
  ⟨[
    (5761, 11447, 5717),
    (5789, 11503, 5749),
    (5813, 11551, 5783),
    (5848, 11621, 5813),
    (5882, 11689, 5849),
    (5909, 11743, 5881),
    (5944, 11813, 5903),
    (5972, 11867, 5939),
    (6000, 11923, 5953),
    (6032, 11987, 5987),
    (6063, 12049, 6029),
    (6095, 12113, 6053)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk37 : {L : List (ℕ × ℕ × ℕ) // checkSpans 6096 6498 L = true} :=
  ⟨[
    (6120, 12163, 6091),
    (6159, 12241, 6121),
    (6189, 12301, 6151),
    (6212, 12347, 6173),
    (6249, 12421, 6211),
    (6288, 12497, 6247),
    (6324, 12569, 6287),
    (6363, 12647, 6323),
    (6400, 12721, 6361),
    (6435, 12791, 6397),
    (6466, 12853, 6427),
    (6498, 12917, 6451)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk38 : {L : List (ℕ × ℕ × ℕ) // checkSpans 6499 6922 L = true} :=
  ⟨[
    (6531, 12983, 6491),
    (6564, 13049, 6529),
    (6604, 13127, 6563),
    (6634, 13187, 6599),
    (6665, 13249, 6619),
    (6704, 13327, 6661),
    (6740, 13399, 6703),
    (6779, 13477, 6737),
    (6817, 13553, 6779),
    (6850, 13619, 6803),
    (6886, 13691, 6841),
    (6922, 13763, 6883)
  ], by decide +kernel⟩

set_option maxRecDepth 4096 in
private def chunk39 : {L : List (ℕ × ℕ × ℕ) // checkSpans 6923 7000 L = true} :=
  ⟨[
    (6957, 13831, 6917),
    (6995, 13907, 6949),
    (7000, 13967, 6991)
  ], by decide +kernel⟩

/-- The finite numerical window, verified by 471 explicit prime certificates
on contiguous subintervals, including the exceptional p = 43 and p = 113. -/
theorem small_range (n : ℕ) (hlo : 10 ≤ n) (hhi : n ≤ 7000) :
    ∃ p : ℕ, WindowCertificate n p := by
  by_cases h0 : n ≤ 23
  · exact checkSpans_sound chunk0.2 (by omega) h0
  by_cases h1 : n ≤ 40
  · exact checkSpans_sound chunk1.2 (by omega) h1
  by_cases h2 : n ≤ 62
  · exact checkSpans_sound chunk2.2 (by omega) h2
  by_cases h3 : n ≤ 86
  · exact checkSpans_sound chunk3.2 (by omega) h3
  by_cases h4 : n ≤ 116
  · exact checkSpans_sound chunk4.2 (by omega) h4
  by_cases h5 : n ≤ 147
  · exact checkSpans_sound chunk5.2 (by omega) h5
  by_cases h6 : n ≤ 181
  · exact checkSpans_sound chunk6.2 (by omega) h6
  by_cases h7 : n ≤ 222
  · exact checkSpans_sound chunk7.2 (by omega) h7
  by_cases h8 : n ≤ 289
  · exact checkSpans_sound chunk8.2 (by omega) h8
  by_cases h9 : n ≤ 354
  · exact checkSpans_sound chunk9.2 (by omega) h9
  by_cases h10 : n ≤ 430
  · exact checkSpans_sound chunk10.2 (by omega) h10
  by_cases h11 : n ≤ 509
  · exact checkSpans_sound chunk11.2 (by omega) h11
  by_cases h12 : n ≤ 612
  · exact checkSpans_sound chunk12.2 (by omega) h12
  by_cases h13 : n ≤ 682
  · exact checkSpans_sound chunk13.2 (by omega) h13
  by_cases h14 : n ≤ 799
  · exact checkSpans_sound chunk14.2 (by omega) h14
  by_cases h15 : n ≤ 903
  · exact checkSpans_sound chunk15.2 (by omega) h15
  by_cases h16 : n ≤ 1030
  · exact checkSpans_sound chunk16.2 (by omega) h16
  by_cases h17 : n ≤ 1165
  · exact checkSpans_sound chunk17.2 (by omega) h17
  by_cases h18 : n ≤ 1328
  · exact checkSpans_sound chunk18.2 (by omega) h18
  by_cases h19 : n ≤ 1462
  · exact checkSpans_sound chunk19.2 (by omega) h19
  by_cases h20 : n ≤ 1634
  · exact checkSpans_sound chunk20.2 (by omega) h20
  by_cases h21 : n ≤ 1785
  · exact checkSpans_sound chunk21.2 (by omega) h21
  by_cases h22 : n ≤ 1980
  · exact checkSpans_sound chunk22.2 (by omega) h22
  by_cases h23 : n ≤ 2204
  · exact checkSpans_sound chunk23.2 (by omega) h23
  by_cases h24 : n ≤ 2425
  · exact checkSpans_sound chunk24.2 (by omega) h24
  by_cases h25 : n ≤ 2662
  · exact checkSpans_sound chunk25.2 (by omega) h25
  by_cases h26 : n ≤ 2901
  · exact checkSpans_sound chunk26.2 (by omega) h26
  by_cases h27 : n ≤ 3163
  · exact checkSpans_sound chunk27.2 (by omega) h27
  by_cases h28 : n ≤ 3430
  · exact checkSpans_sound chunk28.2 (by omega) h28
  by_cases h29 : n ≤ 3726
  · exact checkSpans_sound chunk29.2 (by omega) h29
  by_cases h30 : n ≤ 4037
  · exact checkSpans_sound chunk30.2 (by omega) h30
  by_cases h31 : n ≤ 4337
  · exact checkSpans_sound chunk31.2 (by omega) h31
  by_cases h32 : n ≤ 4662
  · exact checkSpans_sound chunk32.2 (by omega) h32
  by_cases h33 : n ≤ 5009
  · exact checkSpans_sound chunk33.2 (by omega) h33
  by_cases h34 : n ≤ 5370
  · exact checkSpans_sound chunk34.2 (by omega) h34
  by_cases h35 : n ≤ 5729
  · exact checkSpans_sound chunk35.2 (by omega) h35
  by_cases h36 : n ≤ 6095
  · exact checkSpans_sound chunk36.2 (by omega) h36
  by_cases h37 : n ≤ 6498
  · exact checkSpans_sound chunk37.2 (by omega) h37
  by_cases h38 : n ≤ 6922
  · exact checkSpans_sound chunk38.2 (by omega) h38
  exact checkSpans_sound chunk39.2 (by omega) hhi

end OMA.Erdos402Window

theorem OMA.solution : OMA.R_Erdos402_erdos_402_variants_equality_R1_H1_R1.H1 := by
  intro n hlo hhi
  exact OMA.Erdos402Window.small_range n hlo hhi
