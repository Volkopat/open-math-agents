import OMAStatements.S_oeis_a015762

-- Problem: A015762: Numbers n such that phi(n) | sigma_4(n)
-- Upstream: statements/oeis-a015762.lean (declaration OMA.S_oeis_a015762.main)
-- Credit: @Raimo33 (the owner of the agent is credited as the solver)
-- Counterexample: n = prod_(p,e) p^e over 38 primes (including 2^2, 43, 137^15),
-- where phi(n) | sigma_4(n), 7 | 42 = phi(43) | phi(n), and 7 does not divide sigma_12(n).

namespace OMA.DisproofA015762

open ArithmeticFunction

private def powMod (a e m : ℕ) : ℕ :=
  if h : e = 0 then 1 % m
  else
    let half := powMod a (e / 2) m
    let sq := (half * half) % m
    if e % 2 = 0 then sq else (sq * a) % m
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

private theorem powMod_eq (a e m : ℕ) : powMod a e m = a ^ e % m := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    unfold powMod
    split_ifs with h0 heven
    · subst h0; simp
    · have hlt : e / 2 < e := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
      rw [ih (e / 2) hlt]
      have he : e = e / 2 + e / 2 := by omega
      conv_rhs => rw [he, pow_add, Nat.mul_mod]
    · have hlt : e / 2 < e := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
      rw [ih (e / 2) hlt]
      have he : e = e / 2 + e / 2 + 1 := by omega
      dsimp only
      conv_rhs => rw [he, pow_succ, pow_add]
      rw [← Nat.mul_mod (a ^ (e / 2)) (a ^ (e / 2)) m,
          Nat.mul_mod (a ^ (e / 2) * a ^ (e / 2) % m) a m, Nat.mod_mod, ← Nat.mul_mod]

private def prodPow (L : List (ℕ × ℕ)) : ℕ :=
  (L.map (fun qc => qc.1 ^ qc.2)).prod

private def checkSmallPrime (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range 32).all (fun d => decide (d < 2) || decide (p < d * d) || decide (p % d ≠ 0))

private theorem checkSmallPrime_sound {p : ℕ} (hp : p < 1000) (h : checkSmallPrime p = true) :
    p.Prime := by
  unfold checkSmallPrime at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at h
  rw [Nat.prime_def]
  refine ⟨h.1, fun d hd => ?_⟩
  by_contra hne
  push Not at hne
  have hd_gt : 1 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · simp at hd; omega
    · omega
  have hd_lt : d < p := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd) hne.2
  have hmin : min d (p / d) < 32 := by
    have hmul : min d (p / d) * min d (p / d) ≤ p := by
      calc min d (p / d) * min d (p / d)
          ≤ d * (p / d) := Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)
        _ = p := Nat.mul_div_cancel' hd
    by_contra hge
    have : 32 * 32 ≤ min d (p / d) * min d (p / d) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hmem := h.2 (min d (p / d)) (List.mem_range.mpr hmin)
  have hmin_ge2 : 2 ≤ min d (p / d) := by
    have hq : 2 ≤ p / d := by
      have : d * (p / d) = p := Nat.mul_div_cancel' hd
      by_contra hlt
      have hle : p / d ≤ 1 := by omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hz | ho
      · rw [hz, mul_zero] at this; omega
      · rw [ho, mul_one] at this; exact hne.2 this
    exact le_min (by omega) hq
  have hmin_sq : min d (p / d) * min d (p / d) ≤ p := by
    calc min d (p / d) * min d (p / d)
        ≤ d * (p / d) := Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)
      _ = p := Nat.mul_div_cancel' hd
  have hmin_dvd : min d (p / d) ∣ p := by
    rcases le_total d (p / d) with hle | hle
    · rw [min_eq_left hle]; exact hd
    · rw [min_eq_right hle]; exact Nat.div_dvd_of_dvd hd
  have hmod0 : p % min d (p / d) = 0 := Nat.mod_eq_zero_of_dvd hmin_dvd
  rcases hmem with (h1 | h2) | h3
  · omega
  · omega
  · exact h3 hmod0

private lemma prime_dvd_prodPow {q : ℕ} (hq : q.Prime) :
    ∀ {L : List (ℕ × ℕ)}, (∀ qc ∈ L, qc.1.Prime) → q ∣ prodPow L → ∃ qc ∈ L, q = qc.1
  | [], _, hdvd => by
    simp only [prodPow, List.map_nil, List.prod_nil] at hdvd
    exact absurd (Nat.eq_one_of_dvd_one hdvd) hq.ne_one
  | qc :: t, hall, hdvd => by
    simp only [prodPow, List.map_cons, List.prod_cons] at hdvd
    rcases hq.dvd_mul.mp hdvd with h1 | h2
    · have h1' : q ∣ qc.1 := hq.dvd_of_dvd_pow h1
      have hqp : qc.1.Prime := hall qc (by simp)
      exact ⟨qc, by simp, (Nat.prime_dvd_prime_iff_eq hq hqp).mp h1'⟩
    · obtain ⟨x, hx, heq⟩ := prime_dvd_prodPow hq (fun y hy => hall y (by simp [hy])) h2
      exact ⟨x, by simp [hx], heq⟩

private def checkPrattEntry (verified : List ℕ) (e : ℕ × ℕ × List (ℕ × ℕ)) : Bool :=
  let p := e.1
  let a := e.2.1
  let facs := e.2.2
  if facs.isEmpty then
    decide (p < 1000) && checkSmallPrime p
  else
    decide (2 ≤ p) &&
    decide (prodPow facs = p - 1) &&
    facs.all (fun qc => verified.contains qc.1) &&
    decide (powMod a (p - 1) p = 1) &&
    facs.all (fun qc => decide (powMod a ((p - 1) / qc.1) p ≠ 1))

private theorem checkPrattEntry_sound {verified : List ℕ} (hv : ∀ q ∈ verified, q.Prime)
    {e : ℕ × ℕ × List (ℕ × ℕ)} (hc : checkPrattEntry verified e = true) : e.1.Prime := by
  unfold checkPrattEntry at hc
  dsimp only at hc
  split_ifs at hc with hemp
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact checkSmallPrime_sound hc.1 hc.2
  · simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.contains_eq_mem] at hc
    rcases hc with ⟨⟨⟨⟨hp2, hprod⟩, hmem⟩, ha1⟩, hane⟩
    have : NeZero e.1 := ⟨by omega⟩
    have : Fact (1 < e.1) := ⟨by omega⟩
    apply lucas_primality e.1 (e.2.1 : ZMod e.1)
    · have hpow : e.2.1 ^ (e.1 - 1) % e.1 = 1 := by rw [← powMod_eq]; exact ha1
      apply ZMod.val_injective e.1
      rw [← Nat.cast_pow, ZMod.val_natCast, hpow, ZMod.val_one]
    · intro q hq hqdvd
      have hallp : ∀ qc ∈ e.2.2, qc.1.Prime := fun qc hqc => hv qc.1 (hmem qc hqc)
      rw [← hprod] at hqdvd
      obtain ⟨qc, hqc, rfl⟩ := prime_dvd_prodPow hq hallp hqdvd
      have hne : e.2.1 ^ ((e.1 - 1) / qc.1) % e.1 ≠ 1 := by
        rw [← powMod_eq]; exact hane qc hqc
      intro heq
      apply hne
      have hval := congrArg ZMod.val heq
      rw [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_one] at hval
      exact hval

private def checkPrattList : List ℕ → List (ℕ × ℕ × List (ℕ × ℕ)) → Bool
  | _, [] => true
  | verified, e :: rest => checkPrattEntry verified e && checkPrattList (e.1 :: verified) rest

private theorem checkPrattList_sound :
    ∀ (verified : List ℕ) (L : List (ℕ × ℕ × List (ℕ × ℕ))),
      (∀ q ∈ verified, q.Prime) →
      checkPrattList verified L = true →
      ∀ e ∈ L, e.1.Prime
  | _, [], _, _, _, h => by simp at h
  | verified, e :: rest, hv, hc, x, hx => by
    simp only [checkPrattList, Bool.and_eq_true] at hc
    have he : e.1.Prime := checkPrattEntry_sound hv hc.1
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hrest
    · exact he
    · apply checkPrattList_sound (e.1 :: verified) rest ?_ hc.2 x hrest
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq'
      · exact he
      · exact hv q hq'

private def prattCert : List (ℕ × ℕ × List (ℕ × ℕ)) := [
  (2, 0, []),
  (3, 0, []),
  (5, 0, []),
  (7, 0, []),
  (11, 0, []),
  (13, 0, []),
  (17, 0, []),
  (19, 0, []),
  (29, 0, []),
  (31, 0, []),
  (37, 0, []),
  (41, 0, []),
  (43, 0, []),
  (47, 0, []),
  (59, 0, []),
  (71, 0, []),
  (73, 0, []),
  (83, 0, []),
  (89, 0, []),
  (97, 0, []),
  (103, 0, []),
  (113, 0, []),
  (127, 0, []),
  (137, 0, []),
  (151, 0, []),
  (179, 0, []),
  (193, 0, []),
  (199, 0, []),
  (223, 0, []),
  (227, 0, []),
  (229, 0, []),
  (233, 0, []),
  (239, 0, []),
  (241, 0, []),
  (257, 0, []),
  (311, 0, []),
  (337, 0, []),
  (349, 0, []),
  (353, 0, []),
  (373, 0, []),
  (421, 0, []),
  (449, 0, []),
  (521, 0, []),
  (557, 0, []),
  (577, 0, []),
  (617, 0, []),
  (673, 0, []),
  (809, 0, []),
  (821, 0, []),
  (881, 0, []),
  (929, 0, []),
  (937, 0, []),
  (947, 0, []),
  (977, 0, []),
  (1093, 5, [(2, 2), (3, 1), (7, 1), (13, 1)]),
  (1129, 11, [(2, 3), (3, 1), (47, 1)]),
  (1201, 11, [(2, 4), (3, 1), (5, 2)]),
  (1361, 3, [(2, 4), (5, 1), (17, 1)]),
  (1409, 3, [(2, 7), (11, 1)]),
  (1549, 2, [(2, 2), (3, 2), (43, 1)]),
  (1601, 3, [(2, 6), (5, 2)]),
  (1721, 3, [(2, 3), (5, 1), (43, 1)]),
  (2003, 5, [(2, 1), (7, 1), (11, 1), (13, 1)]),
  (2137, 10, [(2, 3), (3, 1), (89, 1)]),
  (2239, 3, [(2, 1), (3, 1), (373, 1)]),
  (2267, 2, [(2, 1), (11, 1), (103, 1)]),
  (2273, 3, [(2, 5), (71, 1)]),
  (2297, 5, [(2, 3), (7, 1), (41, 1)]),
  (2377, 5, [(2, 3), (3, 3), (11, 1)]),
  (2411, 6, [(2, 1), (5, 1), (241, 1)]),
  (2677, 2, [(2, 2), (3, 1), (223, 1)]),
  (2953, 13, [(2, 3), (3, 2), (41, 1)]),
  (3049, 11, [(2, 3), (3, 1), (127, 1)]),
  (3257, 3, [(2, 3), (11, 1), (37, 1)]),
  (3593, 3, [(2, 3), (449, 1)]),
  (3709, 2, [(2, 2), (3, 2), (103, 1)]),
  (3733, 2, [(2, 2), (3, 1), (311, 1)]),
  (4007, 5, [(2, 1), (2003, 1)]),
  (4211, 6, [(2, 1), (5, 1), (421, 1)]),
  (4457, 3, [(2, 3), (557, 1)]),
  (4547, 2, [(2, 1), (2273, 1)]),
  (5039, 11, [(2, 1), (11, 1), (229, 1)]),
  (5393, 3, [(2, 4), (337, 1)]),
  (5801, 3, [(2, 3), (5, 2), (29, 1)]),
  (5987, 2, [(2, 1), (41, 1), (73, 1)]),
  (6197, 2, [(2, 2), (1549, 1)]),
  (6359, 13, [(2, 1), (11, 1), (17, 2)]),
  (6563, 5, [(2, 1), (17, 1), (193, 1)]),
  (6569, 3, [(2, 3), (821, 1)]),
  (7577, 3, [(2, 3), (947, 1)]),
  (8377, 5, [(2, 3), (3, 1), (349, 1)]),
  (8423, 5, [(2, 1), (4211, 1)]),
  (12377, 6, [(2, 3), (7, 1), (13, 1), (17, 1)]),
  (14009, 3, [(2, 3), (17, 1), (103, 1)]),
  (16063, 5, [(2, 1), (3, 1), (2677, 1)]),
  (19121, 6, [(2, 4), (5, 1), (239, 1)]),
  (19417, 5, [(2, 3), (3, 1), (809, 1)]),
  (21481, 13, [(2, 3), (3, 1), (5, 1), (179, 1)]),
  (21577, 5, [(2, 3), (3, 1), (29, 1), (31, 1)]),
  (28019, 2, [(2, 1), (14009, 1)]),
  (35401, 13, [(2, 3), (3, 1), (5, 2), (59, 1)]),
  (49529, 3, [(2, 3), (41, 1), (151, 1)]),
  (60649, 11, [(2, 3), (3, 1), (7, 1), (19, 2)]),
  (100403, 2, [(2, 1), (17, 1), (2953, 1)]),
  (262261, 2, [(2, 2), (3, 2), (5, 1), (31, 1), (47, 1)]),
  (296579, 2, [(2, 1), (257, 1), (577, 1)]),
  (320561, 3, [(2, 4), (5, 1), (4007, 1)]),
  (332729, 3, [(2, 3), (11, 1), (19, 1), (199, 1)]),
  (347033, 3, [(2, 3), (7, 1), (6197, 1)]),
  (423277, 2, [(2, 2), (3, 1), (7, 1), (5039, 1)]),
  (535013, 2, [(2, 2), (59, 1), (2267, 1)]),
  (1005241, 14, [(2, 3), (3, 1), (5, 1), (8377, 1)]),
  (1095793, 7, [(2, 4), (3, 1), (37, 1), (617, 1)]),
  (1669177, 7, [(2, 3), (3, 2), (97, 1), (239, 1)]),
  (2853577, 5, [(2, 3), (3, 3), (11, 1), (1201, 1)]),
  (2902883, 2, [(2, 1), (41, 1), (35401, 1)]),
  (3156991, 3, [(2, 1), (3, 1), (5, 1), (47, 1), (2239, 1)]),
  (3583681, 21, [(2, 6), (3, 1), (5, 1), (3733, 1)]),
  (4196177, 3, [(2, 4), (262261, 1)]),
  (12840313, 11, [(2, 3), (3, 1), (535013, 1)]),
  (13228861, 6, [(2, 2), (3, 1), (5, 1), (97, 1), (2273, 1)]),
  (18504193, 5, [(2, 9), (3, 1), (7, 1), (1721, 1)]),
  (25112977, 5, [(2, 4), (3, 1), (7, 1), (31, 1), (2411, 1)]),
  (27983723, 2, [(2, 1), (13, 1), (353, 1), (3049, 1)]),
  (29391169, 14, [(2, 6), (3, 1), (47, 1), (3257, 1)]),
  (34376723, 2, [(2, 1), (73, 1), (241, 1), (977, 1)]),
  (36185209, 17, [(2, 3), (3, 1), (179, 1), (8423, 1)]),
  (173083139, 2, [(2, 1), (4457, 1), (19417, 1)]),
  (227303353, 5, [(2, 3), (3, 2), (3156991, 1)]),
  (308167513, 5, [(2, 3), (3, 1), (12840313, 1)]),
  (321690521, 3, [(2, 3), (5, 1), (19, 1), (423277, 1)]),
  (397978739, 6, [(2, 1), (17, 1), (193, 1), (60649, 1)]),
  (463824227, 2, [(2, 1), (17, 1), (41, 1), (332729, 1)]),
  (649743443, 2, [(2, 1), (97, 1), (1409, 1), (2377, 1)]),
  (927294817, 10, [(2, 5), (3, 1), (7, 2), (31, 1), (6359, 1)]),
  (1466738579, 2, [(2, 1), (257, 1), (2853577, 1)]),
  (2043184249, 13, [(2, 3), (3, 2), (7, 1), (1093, 1), (3709, 1)]),
  (3508729187, 2, [(2, 1), (1601, 1), (1095793, 1)]),
  (10252052627, 2, [(2, 1), (353, 1), (673, 1), (21577, 1)]),
  (13695007043, 2, [(2, 1), (41, 1), (521, 1), (320561, 1)]),
  (21929647427, 2, [(2, 1), (6569, 1), (1669177, 1)]),
  (233251277153, 3, [(2, 5), (19, 1), (29, 1), (13228861, 1)]),
  (287817152387, 2, [(2, 1), (41, 1), (97, 1), (36185209, 1)]),
  (309676803587, 2, [(2, 1), (1361, 1), (2297, 1), (49529, 1)]),
  (734233681619, 2, [(2, 1), (937, 1), (1129, 1), (347033, 1)]),
  (1465384904003, 2, [(2, 1), (97, 1), (257, 1), (29391169, 1)]),
  (1700643193763, 2, [(2, 1), (3593, 1), (12377, 1), (19121, 1)]),
  (3058218306467, 2, [(2, 1), (17, 1), (97, 1), (927294817, 1)]),
  (3319755079427, 2, [(2, 1), (449, 1), (881, 1), (4196177, 1)]),
  (14229170259827, 2, [(2, 1), (929, 1), (2137, 1), (3583681, 1)]),
  (14337361547801, 3, [(2, 3), (5, 2), (19, 1), (31, 1), (7577, 1), (16063, 1)]),
  (18341363203859, 6, [(2, 1), (17, 1), (21481, 1), (25112977, 1)]),
  (34054686464339, 2, [(2, 1), (73, 1), (233251277153, 1)]),
  (20128042719094307, 2, [(2, 1), (5393, 1), (5801, 1), (321690521, 1)]),
  (106478506840852019, 2, [(2, 1), (233, 1), (1005241, 1), (227303353, 1)]),
  (467596073224324739, 2, [(2, 1), (41, 1), (18504193, 1), (308167513, 1)]),
  (58587742573370527572899, 2, [(2, 1), (2043184249, 1), (14337361547801, 1)])
]

private def verifiedPrimes : List ℕ := prattCert.map Prod.fst

set_option maxHeartbeats 4000000 in
private theorem prattCert_ok : checkPrattList [] prattCert = true := by
  decide +kernel

private theorem mem_verifiedPrimes_prime {q : ℕ} (hq : q ∈ verifiedPrimes) : q.Prime := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  exact checkPrattList_sound [] prattCert (by simp) prattCert_ok e he

private lemma finset_sum_range_eq_list_sum (n : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range n, f i) = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]
    simp

private def natListSum : List ℕ → ℕ
  | [] => 0
  | a :: t => a + natListSum t

private lemma natListSum_eq_sum : ∀ l : List ℕ, natListSum l = l.sum
  | [] => rfl
  | a :: t => by simp [natListSum, natListSum_eq_sum t]

private def sig4Mod (p e m : ℕ) : ℕ :=
  natListSum ((List.range (e + 1)).map (fun i => powMod p (4 * i) m)) % m

private lemma sum_mod_eq_sum_map_mod {ι : Type*} (l : List ι) (f : ι → ℕ) (m : ℕ) :
    (l.map f).sum % m = (l.map (fun x => f x % m)).sum % m := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Nat.add_mod, ih, ← Nat.add_mod, Nat.add_mod (f a % m), Nat.mod_mod, ← Nat.add_mod]

private theorem dvd_sigma4_prime_pow {p e m : ℕ} (hp : p.Prime)
    (h : sig4Mod p e m = 0) : m ∣ ArithmeticFunction.sigma 4 (p ^ e) := by
  rw [sigma_apply_prime_pow hp, Nat.dvd_iff_mod_eq_zero]
  have hsum : (∑ j ∈ Finset.range (e + 1), p ^ (j * 4)) =
      ((List.range (e + 1)).map (fun i => p ^ (4 * i))).sum := by
    rw [finset_sum_range_eq_list_sum]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [Nat.mul_comm]
  rw [hsum, sum_mod_eq_sum_map_mod]
  have hmap : ((List.range (e + 1)).map (fun i => p ^ (4 * i) % m)) =
      ((List.range (e + 1)).map (fun i => powMod p (4 * i) m)) := by
    apply List.map_congr_left
    intro i _
    exact (powMod_eq p (4 * i) m).symm
  rw [hmap, ← natListSum_eq_sum]
  exact h

private def isSortedFst : List (ℕ × ℕ) → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (a.1 < b.1) && isSortedFst (b :: t)

private lemma isSortedFst_tail {a : ℕ × ℕ} {t : List (ℕ × ℕ)} (h : isSortedFst (a :: t) = true) :
    isSortedFst t = true := by
  cases t with
  | nil => rfl
  | cons b r =>
    simp only [isSortedFst, Bool.and_eq_true] at h
    exact h.2

private lemma isSortedFst_lt :
    ∀ {a : ℕ × ℕ} {t : List (ℕ × ℕ)}, isSortedFst (a :: t) = true → ∀ x ∈ t, a.1 < x.1
  | _, [], _, _, h => by simp at h
  | a, b :: r, h, x, hx => by
    simp only [isSortedFst, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hr
    · exact h.1
    · exact lt_trans h.1 (isSortedFst_lt h.2 x hr)

private lemma coprime_prodPow_of_lt {p : ℕ} (hp : p.Prime) :
    ∀ {L : List (ℕ × ℕ)}, (∀ qc ∈ L, qc.1.Prime ∧ p < qc.1) →
      Nat.Coprime p (prodPow L)
  | [], _ => by simp [prodPow]
  | qc :: t, hall => by
    simp only [prodPow, List.map_cons, List.prod_cons]
    have h1 := hall qc (by simp)
    have hcop1 : Nat.Coprime p (qc.1 ^ qc.2) :=
      ((Nat.coprime_primes hp h1.1).mpr (by omega)).pow_right qc.2
    exact hcop1.mul_right (coprime_prodPow_of_lt hp (fun x hx => hall x (by simp [hx])))

private lemma prodPow_dvd_of_sorted {M : ℕ} :
    ∀ {L : List (ℕ × ℕ)},
      isSortedFst L = true →
      (∀ qc ∈ L, qc.1.Prime) →
      (∀ qc ∈ L, qc.1 ^ qc.2 ∣ M) →
      prodPow L ∣ M
  | [], _, _, _ => by simp [prodPow]
  | qc :: t, hs, hall, hdvd => by
    simp only [prodPow, List.map_cons, List.prod_cons]
    have hlt := isSortedFst_lt hs
    have hts := isSortedFst_tail hs
    have hcop : Nat.Coprime (qc.1 ^ qc.2) (prodPow t) :=
      (coprime_prodPow_of_lt (hall qc (by simp)) (fun x hx => ⟨hall x (by simp [hx]), hlt x hx⟩)).pow_left qc.2
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd qc (by simp))
      (prodPow_dvd_of_sorted hts (fun x hx => hall x (by simp [hx])) (fun x hx => hdvd x (by simp [hx])))

private def expandPow : List (ℕ × ℕ) → List ℕ
  | [] => []
  | (q, c) :: t => List.replicate c q ++ expandPow t

private lemma prod_expandPow (L : List (ℕ × ℕ)) : (expandPow L).prod = prodPow L := by
  induction L with
  | nil => simp [expandPow, prodPow]
  | cons qc t ih =>
    rcases qc with ⟨q, c⟩
    simp [expandPow, prodPow, ih]

private def insOne (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: t => if x ≤ y then x :: y :: t else y :: insOne x t

private lemma insOne_perm (x : ℕ) (L : List ℕ) : (x :: L).Perm (insOne x L) := by
  induction L with
  | nil => simp [insOne]
  | cons y t ih =>
    unfold insOne
    split_ifs
    · exact List.Perm.refl _
    · exact (List.Perm.swap y x t).trans (List.Perm.cons y ih)

private def insSort : List ℕ → List ℕ
  | [] => []
  | x :: t => insOne x (insSort t)

private lemma insSort_perm (L : List ℕ) : L.Perm (insSort L) := by
  induction L with
  | nil => simp [insSort]
  | cons x t ih =>
    simp only [insSort]
    exact (List.Perm.cons x ih).trans (insOne_perm x (insSort t))

private lemma list_prod_dvd_of_forall_dvd :
    ∀ {α : Type*} (L : List α) (f g : α → ℕ), (∀ x ∈ L, f x ∣ g x) → (L.map f).prod ∣ (L.map g).prod
  | _, [], _, _, _ => by simp
  | _, a :: t, f, g, h => by
    simp only [List.map_cons, List.prod_cons]
    exact mul_dvd_mul (h a (by simp)) (list_prod_dvd_of_forall_dvd t f g (fun x hx => h x (by simp [hx])))

private lemma totient_prodPow_of_sorted :
    ∀ {L : List (ℕ × ℕ)},
      isSortedFst L = true →
      (∀ pe ∈ L, pe.1.Prime ∧ 1 ≤ pe.2) →
      Nat.totient (prodPow L) = (L.map (fun pe => (pe.1 - 1) * pe.1 ^ (pe.2 - 1))).prod
  | [], _, _ => by simp [prodPow]
  | pe :: t, hs, hall => by
    simp only [prodPow, List.map_cons, List.prod_cons]
    have hlt := isSortedFst_lt hs
    have hts := isSortedFst_tail hs
    have hpe := hall pe (by simp)
    have hcop : Nat.Coprime (pe.1 ^ pe.2) (prodPow t) :=
      (coprime_prodPow_of_lt hpe.1 (fun x hx => ⟨(hall x (by simp [hx])).1, hlt x hx⟩)).pow_left pe.2
    change Nat.totient (pe.1 ^ pe.2 * prodPow t) = _
    rw [Nat.totient_mul hcop, Nat.totient_prime_pow hpe.1 (by omega), Nat.mul_comm (pe.1 ^ (pe.2 - 1)),
        totient_prodPow_of_sorted hts (fun x hx => hall x (by simp [hx]))]

private lemma sigma_prodPow_of_sorted (m : ℕ) :
    ∀ {L : List (ℕ × ℕ)},
      isSortedFst L = true →
      (∀ pe ∈ L, pe.1.Prime) →
      ArithmeticFunction.sigma m (prodPow L) = (L.map (fun pe => ArithmeticFunction.sigma m (pe.1 ^ pe.2))).prod
  | [], _, _ => by simp [prodPow]
  | pe :: t, hs, hall => by
    simp only [prodPow, List.map_cons, List.prod_cons]
    have hlt := isSortedFst_lt hs
    have hts := isSortedFst_tail hs
    have hpe := hall pe (by simp)
    have hcop : Nat.Coprime (pe.1 ^ pe.2) (prodPow t) :=
      (coprime_prodPow_of_lt hpe (fun x hx => ⟨hall x (by simp [hx]), hlt x hx⟩)).pow_left pe.2
    change ArithmeticFunction.sigma m (pe.1 ^ pe.2 * prodPow t) = _
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop,
        sigma_prodPow_of_sorted m hts (fun x hx => hall x (by simp [hx]))]

private def witnessData : List (ℕ × ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)) := [
  (2, 2, [(2, 1)], [(3, 1), (7, 1), (13, 1)]),
  (3, 1, [(2, 1)], [(2, 1), (41, 1)]),
  (43, 1, [(2, 1), (3, 1), (7, 1)], [(2, 1), (17, 1), (193, 1), (521, 1)]),
  (83, 1, [(2, 1), (41, 1)], [(2, 1), (17, 1), (73, 1), (19121, 1)]),
  (137, 15, [(2, 3), (17, 1), (137, 14)], [(2, 4), (41, 1), (257, 1), (353, 1), (1409, 1), (1601, 1), (3049, 1), (1095793, 1), (29391169, 1)]),
  (227, 1, [(2, 1), (113, 1)], [(2, 1), (97, 1), (14009, 1)]),
  (4547, 1, [(2, 1), (2273, 1)], [(2, 1), (17, 1), (1129, 1), (347033, 1)]),
  (5987, 1, [(2, 1), (41, 1), (73, 1)], [(2, 1), (137, 1)]),
  (6563, 1, [(2, 1), (17, 1), (193, 1)], [(2, 1), (41, 1), (97, 1), (233251277153, 1)]),
  (28019, 1, [(2, 1), (14009, 1)], [(2, 1), (2273, 1)]),
  (100403, 1, [(2, 1), (17, 1), (2953, 1)], [(2, 1), (193, 1)]),
  (296579, 1, [(2, 1), (257, 1), (577, 1)], [(2, 1), (97, 1), (19417, 1), (1005241, 1), (2043184249, 1)]),
  (2902883, 1, [(2, 1), (41, 1), (35401, 1)], [(2, 1), (137, 1)]),
  (27983723, 1, [(2, 1), (13, 1), (353, 1), (3049, 1)], [(2, 1), (241, 1), (3593, 1), (12377, 1), (308167513, 1)]),
  (34376723, 1, [(2, 1), (73, 1), (241, 1), (977, 1)], [(2, 1), (41, 1), (233, 1), (937, 1), (1361, 1), (14337361547801, 1)]),
  (173083139, 1, [(2, 1), (4457, 1), (19417, 1)], [(2, 1), (17, 1), (257, 1), (673, 1), (977, 1), (35401, 1)]),
  (397978739, 1, [(2, 1), (17, 1), (193, 1), (60649, 1)], [(2, 1), (137, 1)]),
  (463824227, 1, [(2, 1), (17, 1), (41, 1), (332729, 1)], [(2, 1), (137, 1)]),
  (649743443, 1, [(2, 1), (97, 1), (1409, 1), (2377, 1)], [(2, 1), (17, 1), (5393, 1)]),
  (1466738579, 1, [(2, 1), (257, 1), (2853577, 1)], [(2, 1), (73, 1), (21481, 1), (927294817, 1)]),
  (3508729187, 1, [(2, 1), (1601, 1), (1095793, 1)], [(2, 1), (17, 1), (41, 1), (257, 1), (227303353, 1)]),
  (10252052627, 1, [(2, 1), (353, 1), (673, 1), (21577, 1)], [(2, 1), (41, 1), (137, 1), (18504193, 1), (321690521, 1)]),
  (13695007043, 1, [(2, 1), (41, 1), (521, 1), (320561, 1)], [(2, 1), (449, 1), (929, 1), (2297, 1)]),
  (21929647427, 1, [(2, 1), (6569, 1), (1669177, 1)], [(2, 1), (73, 1), (4457, 1), (2853577, 1), (3583681, 1)]),
  (287817152387, 1, [(2, 1), (41, 1), (97, 1), (36185209, 1)], [(2, 1), (577, 1), (6569, 1), (49529, 1), (1669177, 1)]),
  (309676803587, 1, [(2, 1), (1361, 1), (2297, 1), (49529, 1)], [(2, 1), (113, 1), (2137, 1), (2953, 1)]),
  (734233681619, 1, [(2, 1), (937, 1), (1129, 1), (347033, 1)], [(2, 1), (881, 1)]),
  (1465384904003, 1, [(2, 1), (97, 1), (257, 1), (29391169, 1)], [(2, 1), (353, 1), (320561, 1), (332729, 1), (25112977, 1)]),
  (1700643193763, 1, [(2, 1), (3593, 1), (12377, 1), (19121, 1)], [(2, 1), (137, 1), (36185209, 1)]),
  (3058218306467, 1, [(2, 1), (17, 1), (97, 1), (927294817, 1)], [(2, 1), (137, 1)]),
  (3319755079427, 1, [(2, 1), (449, 1), (881, 1), (4196177, 1)], [(2, 1), (137, 1), (60649, 1)]),
  (14229170259827, 1, [(2, 1), (929, 1), (2137, 1), (3583681, 1)], [(2, 1), (137, 1)]),
  (18341363203859, 1, [(2, 1), (17, 1), (21481, 1), (25112977, 1)], [(2, 1), (41, 1), (97, 1), (2377, 1), (5801, 1), (4196177, 1)]),
  (34054686464339, 1, [(2, 1), (73, 1), (233251277153, 1)], [(2, 1), (17, 1), (137, 1), (21577, 1)]),
  (20128042719094307, 1, [(2, 1), (5393, 1), (5801, 1), (321690521, 1)], [(2, 1), (137, 1)]),
  (106478506840852019, 1, [(2, 1), (233, 1), (1005241, 1), (227303353, 1)], [(2, 1), (137, 1)]),
  (467596073224324739, 1, [(2, 1), (41, 1), (18504193, 1), (308167513, 1)], [(2, 1), (137, 1)]),
  (58587742573370527572899, 1, [(2, 1), (2043184249, 1), (14337361547801, 1)], [(2, 1), (137, 1)])
]

private def peList : List (ℕ × ℕ) := witnessData.map (fun x => (x.1, x.2.1))
private def witnessN : ℕ := prodPow peList

private def checkW1 : Bool := isSortedFst peList
private def checkW2 : Bool := witnessData.all (fun x => verifiedPrimes.contains x.1)
private def checkW3 : Bool := witnessData.all (fun x => decide (1 ≤ x.2.1) && decide (x.1 ≠ 7) && decide ((x.2.1 + 1) % 7 ≠ 0))
private def checkW4 : Bool := witnessData.all (fun x => decide (prodPow x.2.2.1 = (x.1 - 1) * x.1 ^ (x.2.1 - 1)))
private def checkW5 : Bool := witnessData.all (fun x => isSortedFst x.2.2.2)
private def checkW6 : Bool := witnessData.all (fun x => x.2.2.2.all (fun qc => verifiedPrimes.contains qc.1))
private def checkW7 : Bool := witnessData.all (fun x => x.2.2.2.all (fun qc => decide (sig4Mod x.1 x.2.1 (qc.1 ^ qc.2) = 0)))

private theorem checkW1_ok : checkW1 = true := by decide +kernel
private theorem checkW2_ok : checkW2 = true := by decide +kernel
private theorem checkW3_ok : checkW3 = true := by decide +kernel
private theorem checkW4_ok : checkW4 = true := by decide +kernel
private theorem checkW5_ok : checkW5 = true := by decide +kernel
private theorem checkW6_ok : checkW6 = true := by decide +kernel
private theorem checkW7_ok : checkW7 = true := by decide +kernel

private def flatPhi : List ℕ := (witnessData.map (fun x => expandPow x.2.2.1)).flatten
private def flatAssign : List ℕ := (witnessData.map (fun x => expandPow x.2.2.2)).flatten

set_option maxHeartbeats 4000000 in
private theorem flat_sorted_eq : insSort flatPhi = insSort flatAssign := by
  decide +kernel

private theorem flat_prod_eq : flatPhi.prod = flatAssign.prod := by
  have h1 : flatPhi.Perm (insSort flatPhi) := insSort_perm flatPhi
  have h2 : flatAssign.Perm (insSort flatAssign) := insSort_perm flatAssign
  rw [flat_sorted_eq] at h1
  exact (h1.trans h2.symm).prod_eq

private lemma flatten_prod_eq_map_prod :
    ∀ (L : List (List ℕ)), L.flatten.prod = (L.map List.prod).prod
  | [] => by simp
  | a :: t => by simp [flatten_prod_eq_map_prod t]

private theorem peList_sorted : isSortedFst peList = true := checkW1_ok

private theorem witness_all (x) (hx : x ∈ witnessData) :
    x.1.Prime ∧ 1 ≤ x.2.1 ∧ x.1 ≠ 7 ∧ (x.2.1 + 1) % 7 ≠ 0 ∧
    prodPow x.2.2.1 = (x.1 - 1) * x.1 ^ (x.2.1 - 1) ∧
    isSortedFst x.2.2.2 = true ∧
    ∀ qc ∈ x.2.2.2, qc.1.Prime ∧ sig4Mod x.1 x.2.1 (qc.1 ^ qc.2) = 0 := by
  have h2 := checkW2_ok; unfold checkW2 at h2
  have h3 := checkW3_ok; unfold checkW3 at h3
  have h4 := checkW4_ok; unfold checkW4 at h4
  have h5 := checkW5_ok; unfold checkW5 at h5
  have h6 := checkW6_ok; unfold checkW6 at h6
  have h7 := checkW7_ok; unfold checkW7 at h7
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.contains_eq_mem] at h2 h3 h4 h5 h6 h7
  rcases h3 x hx with ⟨⟨he, hne7⟩, he7⟩
  exact ⟨mem_verifiedPrimes_prime (h2 x hx), he, hne7, he7, h4 x hx, h5 x hx, fun qc hqc =>
    ⟨mem_verifiedPrimes_prime (h6 x hx qc hqc), h7 x hx qc hqc⟩⟩

private theorem witnessN_pos : 1 ≤ witnessN := by
  have hall : ∀ pe ∈ peList, 1 ≤ pe.1 ^ pe.2 := by
    intro pe hpe
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpe
    have hp := (witness_all x hx).1
    exact Nat.one_le_pow _ _ hp.pos
  have hpos : ∀ (L : List (ℕ × ℕ)), (∀ pe ∈ L, 1 ≤ pe.1 ^ pe.2) → 1 ≤ prodPow L := by
    intro L
    induction L with
    | nil => intro _; simp [prodPow]
    | cons a t ih =>
      intro hl
      simp only [prodPow, List.map_cons, List.prod_cons]
      exact Nat.mul_pos (hl a (by simp)) (ih (fun x hx => hl x (by simp [hx])))
  exact hpos peList hall

private theorem totient_dvd_sigma4 :
    Nat.totient witnessN ∣ ArithmeticFunction.sigma 4 witnessN := by
  have hall_pe : ∀ pe ∈ peList, pe.1.Prime ∧ 1 ≤ pe.2 := by
    intro pe hpe
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpe
    exact ⟨(witness_all x hx).1, (witness_all x hx).2.1⟩
  rw [witnessN, totient_prodPow_of_sorted peList_sorted hall_pe,
      sigma_prodPow_of_sorted 4 peList_sorted (fun pe hpe => (hall_pe pe hpe).1)]
  have hphi_eq : (peList.map (fun pe => (pe.1 - 1) * pe.1 ^ (pe.2 - 1))).prod = flatPhi.prod := by
    rw [flatPhi, flatten_prod_eq_map_prod, peList, List.map_map, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun x hx => ?_)
    dsimp only [Function.comp]
    rw [prod_expandPow]
    exact (witness_all x hx).2.2.2.2.1.symm
  have hassign_eq : flatAssign.prod = (witnessData.map (fun x => prodPow x.2.2.2)).prod := by
    rw [flatAssign, flatten_prod_eq_map_prod, List.map_map]
    refine congrArg List.prod (List.map_congr_left fun x _ => ?_)
    exact prod_expandPow x.2.2.2
  rw [hphi_eq, flat_prod_eq, hassign_eq, peList, List.map_map]
  apply list_prod_dvd_of_forall_dvd witnessData (fun x => prodPow x.2.2.2)
    (fun x => ArithmeticFunction.sigma 4 (x.1 ^ x.2.1))
  intro x hx
  have hxall := witness_all x hx
  exact prodPow_dvd_of_sorted hxall.2.2.2.2.2.1
    (fun qc hqc => (hxall.2.2.2.2.2.2 qc hqc).1)
    (fun qc hqc => dvd_sigma4_prime_pow hxall.1 (hxall.2.2.2.2.2.2 qc hqc).2)

private theorem seven_dvd_totient : 7 ∣ Nat.totient witnessN := by
  have hall_pe : ∀ pe ∈ peList, pe.1.Prime ∧ 1 ≤ pe.2 := by
    intro pe hpe
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpe
    exact ⟨(witness_all x hx).1, (witness_all x hx).2.1⟩
  rw [witnessN, totient_prodPow_of_sorted peList_sorted hall_pe]
  have h43 : (43, 1) ∈ peList := by decide
  have hmem : (43 - 1) * 43 ^ (1 - 1) ∈ peList.map (fun pe => (pe.1 - 1) * pe.1 ^ (pe.2 - 1)) :=
    List.mem_map.mpr ⟨(43, 1), h43, rfl⟩
  exact dvd_trans (by norm_num : 7 ∣ (43 - 1) * 43 ^ (1 - 1)) (List.dvd_prod hmem)

private lemma pow_twelve_mod_seven {p : ℕ} (hp : p.Prime) (hne : p ≠ 7) : p ^ 12 % 7 = 1 := by
  have hndvd : ¬ 7 ∣ p := fun h => hne ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h).symm
  have hmod : p % 7 ≠ 0 := fun h => hndvd (Nat.dvd_of_mod_eq_zero h)
  rw [Nat.pow_mod]
  have hlt := Nat.mod_lt p (by decide : 0 < 7)
  interval_cases h : p % 7
  · exact False.elim (hmod rfl)
  all_goals norm_num

private lemma not_seven_dvd_sigma12_prime_pow {p e : ℕ} (hp : p.Prime) (hne : p ≠ 7)
    (he7 : (e + 1) % 7 ≠ 0) : ¬ 7 ∣ ArithmeticFunction.sigma 12 (p ^ e) := by
  rw [sigma_apply_prime_pow hp, Nat.dvd_iff_mod_eq_zero]
  have hsum : (∑ j ∈ Finset.range (e + 1), p ^ (j * 12)) =
      ((List.range (e + 1)).map (fun i => (p ^ 12) ^ i)).sum := by
    rw [finset_sum_range_eq_list_sum]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [← pow_mul, Nat.mul_comm]
  rw [hsum, sum_mod_eq_sum_map_mod]
  have h1 : ∀ i ∈ List.range (e + 1), (p ^ 12) ^ i % 7 = 1 := by
    intro i _
    rw [Nat.pow_mod, pow_twelve_mod_seven hp hne, one_pow]
    decide
  rw [List.map_congr_left h1]
  have hrep : ((List.range (e + 1)).map (fun _ => 1)).sum = e + 1 := by
    simp
  rw [hrep]
  exact he7

private lemma not_prime_dvd_list_prod {q : ℕ} (hq : q.Prime) :
    ∀ {L : List ℕ}, (∀ x ∈ L, ¬ q ∣ x) → ¬ q ∣ L.prod
  | [], _ => by simpa using hq.not_dvd_one
  | a :: t, h => by
    simp only [List.prod_cons]
    intro hdvd
    rcases hq.dvd_mul.mp hdvd with h1 | h2
    · exact h a (by simp) h1
    · exact not_prime_dvd_list_prod hq (fun x hx => h x (by simp [hx])) h2

private theorem not_seven_dvd_sigma12 : ¬ 7 ∣ ArithmeticFunction.sigma 12 witnessN := by
  have hall_pe : ∀ pe ∈ peList, pe.1.Prime := by
    intro pe hpe
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpe
    exact (witness_all x hx).1
  rw [witnessN, sigma_prodPow_of_sorted 12 peList_sorted hall_pe]
  apply not_prime_dvd_list_prod (by norm_num : Nat.Prime 7)
  intro y hy
  obtain ⟨pe, hpe, rfl⟩ := List.mem_map.mp hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hpe
  have hxall := witness_all x hx
  exact not_seven_dvd_sigma12_prime_pow hxall.1 hxall.2.2.1 hxall.2.2.2.1

end OMA.DisproofA015762

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a015762.main) := by
  intro h
  have h12 := h OMA.DisproofA015762.witnessN OMA.DisproofA015762.witnessN_pos
    OMA.DisproofA015762.totient_dvd_sigma4 1
  exact OMA.DisproofA015762.not_seven_dvd_sigma12
    (dvd_trans OMA.DisproofA015762.seven_dvd_totient h12)
