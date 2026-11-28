import OMAStatements.S_oeis_a390761

-- Problem: A390761: a(n) is the smallest positive integer k which has the same set of digits as n, and k is divisible by each nonzero digit of n, or -
-- Upstream: formal-conjectures statements/oeis-a390761.lean:0 (declaration OMA.S_oeis_a390761.main)
-- Credit: @m-miyawaki-m (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof sketch. `Valid n k` only depends on the digit set `T` of `n`.
* Upper bound: for each of the 1024 subsets `T ⊆ {0,…,9}` a table gives the least valid `k`
  (computed offline); the kernel checks (`decide +kernel`) that it is valid and `≤ 707777779779`,
  except when `T` contains `5` and an even digit but not `0` — then `10 ∣ k` forces the digit `0`,
  so no valid `k` exists.
* Minimality at 709: digits of `k` lie in `{0,7,9}`, `9 ∣ k` forces `9 ∣ #7s`, hence exactly nine
  7s and at most 12 digits; the ≈2000 remaining digit strings are checked by the kernel.
-/

namespace OMA.Sol_oeis_a390761

open OMA.S_oeis_a390761

def B : ℕ := 707777779779

def tbl : List ℕ := [
0, 0, 1, 10, 2, 20, 12, 102,
3, 30, 1113, 10113, 2232, 20232, 132, 1032,
4, 40, 144, 104, 24, 204, 124, 1024,
3444, 30444, 1344, 10344, 324, 2304, 12324, 102324,
5, 50, 15, 105, 0, 250, 0, 1250,
3555, 30555, 135, 1035, 0, 22350, 0, 112350,
0, 540, 0, 1540, 0, 2540, 0, 12540,
0, 3540, 0, 135540, 0, 234540, 0, 123540,
6, 60, 1116, 10116, 2226, 20226, 126, 1026,
36, 306, 11136, 101136, 22236, 202236, 1236, 10236,
4464, 40464, 1164, 10164, 264, 2064, 12264, 102264,
34464, 304464, 11364, 101364, 2364, 20364, 122364, 1022364,
0, 55560, 0, 1560, 0, 22560, 0, 112560,
0, 355560, 0, 13560, 0, 223560, 0, 1123560,
0, 4560, 0, 145560, 0, 244560, 0, 124560,
0, 34560, 0, 1345560, 0, 2344560, 0, 1234560,
7, 70, 1771, 1071, 2772, 2072, 1722, 2170,
37737, 307377, 3171, 10731, 23772, 2730, 13272, 102732,
44744, 4704, 17444, 7140, 2744, 7420, 4172, 10472,
337344, 30744, 1137444, 17304, 34272, 204372, 117432, 1017324,
5775, 5075, 175, 1750, 0, 22750, 0, 27510,
735, 3570, 13755, 105735, 0, 275730, 0, 125370,
0, 5740, 0, 71540, 0, 245700, 0, 127540,
0, 355740, 0, 1153740, 0, 357420, 0, 12237540,
76776, 677670, 1176, 11760, 672, 6720, 12726, 106722,
677376, 307776, 13776, 110376, 3276, 32760, 132762, 1026732,
7476, 46704, 1764, 17640, 22764, 206472, 112476, 1024716,
34776, 347760, 43176, 107436, 232764, 2023476, 1127364, 10123764,
0, 5670, 0, 175560, 0, 257670, 0, 152670,
0, 36750, 0, 1355760, 0, 2357670, 0, 1263570,
0, 565740, 0, 1145760, 0, 257460, 0, 12254760,
0, 3455760, 0, 11347560, 0, 2357460, 0, 122365740,
8, 80, 1888, 1008, 288, 208, 128, 1208,
3888, 30888, 138888, 13008, 2328, 20328, 11328, 101328,
48, 408, 184, 1048, 248, 2048, 1248, 10248,
384, 3048, 13488, 103488, 23448, 203448, 12384, 102384,
0, 5080, 0, 15080, 0, 5280, 0, 15280,
0, 35880, 0, 1135080, 0, 35280, 0, 1235280,
0, 5480, 0, 15480, 0, 25480, 0, 125480,
0, 345480, 0, 135480, 0, 2235480, 0, 11235480,
6888, 60888, 168, 1608, 2688, 20688, 12168, 102168,
36888, 306888, 1368, 10368, 22368, 202368, 112368, 1012368,
648, 4608, 14688, 104688, 24648, 204648, 12648, 102648,
3648, 30648, 134688, 1034688, 234648, 2034648, 123648, 1023648,
0, 55680, 0, 115680, 0, 25680, 0, 1225680,
0, 355680, 0, 1135680, 0, 235680, 0, 12235680,
0, 445680, 0, 145680, 0, 2245680, 0, 11245680,
0, 3445680, 0, 1345680, 0, 22345680, 0, 112345680,
7888888, 78008, 1777888, 17080, 728, 7280, 11872, 78120,
783888, 37800, 1371888, 137088, 237888, 387072, 37128, 130872,
784, 7840, 14784, 18704, 4872, 27048, 14728, 108472,
337848, 308784, 174384, 1038744, 27384, 203784, 1232784, 10234728,
0, 75880, 0, 157080, 0, 257880, 0, 175280,
0, 3575880, 0, 1375080, 0, 2357880, 0, 11375280,
0, 457800, 0, 175840, 0, 478520, 0, 1257480,
0, 357840, 0, 13587840, 0, 23457840, 0, 12537840,
678888, 76608, 117768, 107688, 67872, 677208, 12768, 127680,
8736, 87360, 138768, 1073688, 277368, 2087736, 167328, 1036728,
87864, 467880, 147168, 1041768, 46872, 207648, 1246728, 10248672,
348768, 3047688, 1137864, 10134768, 243768, 2084376, 12234768, 102263784,
0, 578760, 0, 158760, 0, 2258760, 0, 11257680,
0, 3787560, 0, 1578360, 0, 22578360, 0, 112378560,
0, 547680, 0, 14575680, 0, 24567480, 0, 12475680,
0, 3567480, 0, 134558760, 0, 234567480, 0, 123487560,
9, 90, 1111111119, 10111111119, 2222222292, 20222222292, 122292, 1022292,
3339, 30339, 111339, 1011339, 22392, 202392, 13392, 103392,
4444444944, 40444444944, 1944, 10944, 244944, 2044944, 12492, 102492,
334944, 3034944, 1333944, 113904, 3492, 23904, 1234944, 10234944,
5555555595, 50555555595, 111195, 1011195, 0, 22590, 0, 112590,
35595, 305595, 1395, 10395, 0, 2335590, 0, 12235590,
0, 5940, 0, 1445940, 0, 2255940, 0, 11255940,
0, 3335940, 0, 1355940, 0, 2345940, 0, 12335940,
6696, 60696, 11196, 101196, 222696, 2022696, 1296, 10296,
396, 3096, 1113696, 10113696, 2223396, 20223396, 123696, 1023696,
44496, 404496, 114696, 1014696, 24696, 204696, 1124496, 10124496,
3444696, 30444696, 134496, 1034496, 233496, 2033496, 1223496, 10223496,
0, 5556690, 0, 156690, 0, 255690, 0, 12225690,
0, 33555690, 0, 1335690, 0, 2235690, 0, 11235690,
0, 4566960, 0, 11145960, 0, 24456960, 0, 1245960,
0, 345960, 0, 133455960, 0, 223455960, 0, 123456960,
77777779779, 707777779779, 1197, 11907, 27972, 9072, 177912, 1097712,
373779, 3037797, 13797, 107793, 337932, 2337930, 1233792, 10233972,
4497444, 497700, 1479744, 10791144, 477792, 2797704, 147924, 1044792,
93744, 307944, 11773944, 1373904, 249732, 2037924, 1149372, 10139472,
555975, 5057955, 17955, 159075, 0, 2225790, 0, 11225970,
39375, 303975, 1117935, 10119375, 0, 23359770, 0, 1237950,
0, 4597740, 0, 1157940, 0, 275940, 0, 112579740,
0, 33955740, 0, 13757940, 0, 223459740, 0, 123579540,
97776, 679770, 179676, 1067976, 269766, 2069676, 122976, 1029672,
3776976, 30677976, 117936, 1013796, 29736, 207396, 11273976, 101237976,
446796, 4096764, 91476, 176904, 2264976, 20247696, 1294776, 10274796,
349776, 3407796, 1347696, 10396764, 22349376, 202347936, 12344976, 102367944,
0, 57960, 0, 11597670, 0, 2569770, 0, 12569760,
0, 3567690, 0, 13556970, 0, 222359760, 0, 123359670,
0, 4795560, 0, 14459760, 0, 245669760, 0, 122479560,
0, 344579760, 0, 113457960, 0, 23579640, 0, 11234759760,
8888889888, 80888889888, 1119888, 19008, 8928, 29088, 129888, 1029888,
39888, 309888, 1389888, 10389888, 233928, 2033928, 1133928, 10133928,
489888, 4089888, 114984, 1014984, 24984, 204984, 1122984, 10122984,
33984, 303984, 1113984, 10113984, 2238984, 20238984, 123984, 1023984,
0, 559080, 0, 1559880, 0, 22259880, 0, 1258920,
0, 3359880, 0, 11359080, 0, 358920, 0, 12359880,
0, 5559480, 0, 159480, 0, 2459880, 0, 122559480,
0, 33459480, 0, 113559480, 0, 23559480, 0, 123459480,
669888, 6069888, 166896, 1066896, 22896, 202896, 112896, 1012896,
3369888, 30369888, 13896, 103896, 238896, 2038896, 11236896, 101236896,
4896, 40896, 148896, 1048896, 2469888, 20469888, 1246896, 10246896,
346896, 3046896, 11344896, 101344896, 2344896, 20344896, 12334896, 102334896,
0, 569880, 0, 11568960, 0, 2568960, 0, 12558960,
0, 3558960, 0, 113358960, 0, 23358960, 0, 122358960,
0, 4458960, 0, 144569880, 0, 22458960, 0, 112458960,
0, 344568960, 0, 13458960, 0, 234569880, 0, 11234568960,
7797888, 70797888, 177897888, 11719008, 288792, 2279088, 79128, 109872,
33879888, 379008, 13719888, 1397088, 739872, 3077928, 13339872, 103373928,
98784, 479808, 779184, 1789704, 2298744, 20278944, 11249784, 101297448,
3777984, 30779784, 1378944, 10387944, 2379384, 20397384, 12379248, 102297384,
0, 7597800, 0, 15797880, 0, 5579280, 0, 122587920,
0, 35579880, 0, 133597800, 0, 23589720, 0, 113578920,
0, 45798480, 0, 111759480, 0, 224579880, 0, 12579840,
0, 3759840, 0, 135497880, 0, 235977840, 0, 11235795480,
87696, 687960, 1687896, 10768968, 2289672, 20269872, 11267928, 101227896,
373968, 3073896, 11137896, 101173968, 22398768, 202379688, 1289736, 10239768,
4697784, 40479768, 1169784, 10479168, 247968, 2049768, 12497688, 102487896,
3498768, 30478896, 13477968, 103479768, 23469768, 203476896, 1123449768, 10123467984,
0, 55598760, 0, 1597680, 0, 25789680, 0, 127597680,
0, 35778960, 0, 135976680, 0, 235579680, 0, 11233587960,
0, 45697680, 0, 145587960, 0, 244598760, 0, 11224578960,
0, 334587960, 0, 11134579680, 0, 22345769880, 0, 1234759680]

def maskOf (T : Finset ℕ) : ℕ := T.sum (2 ^ ·)

def bad (T : Finset ℕ) : Prop := 5 ∈ T ∧ (2 ∈ T ∨ 4 ∈ T ∨ 6 ∈ T ∨ 8 ∈ T) ∧ 0 ∉ T

instance (T : Finset ℕ) : Decidable (bad T) := by unfold bad; infer_instance

def digs : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, k => if k = 0 then [] else k % 10 :: digs f (k / 10)

def goodW (T : Finset ℕ) (w : ℕ) : Prop :=
  0 < w ∧ w ≤ B ∧ (digs 13 w).toFinset = T ∧ ∀ d ∈ T, d ≠ 0 → w % d = 0

instance (T : Finset ℕ) (w : ℕ) : Decidable (goodW T w) := by unfold goodW; infer_instance

set_option maxRecDepth 100000 in
theorem table_ok : ∀ T ∈ (Finset.range 10).powerset,
    T = ∅ ∨ T = {0} ∨ bad T ∨ goodW T (tbl.getD (maskOf T) 0) := by
  decide +kernel

lemma digs_eq : ∀ f k : ℕ, k < 10 ^ f → digs f k = Nat.digits 10 k := by
  intro f
  induction f with
  | zero => intro k hk; simp at hk; subst hk; simp [digs]
  | succ f ih =>
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp [digs]
    · rw [digs, if_neg hpos.ne', Nat.digits_def' (by norm_num) hpos, ih]
      rw [pow_succ] at hk; omega

lemma bad_false (n j : ℕ) (hb : bad (Nat.digits 10 n).toFinset) (hv : Valid n j) : False := by
  obtain ⟨h5, hev, h0⟩ := hb
  obtain ⟨hj, hT, hd⟩ := hv
  simp only [List.mem_toFinset] at h5 hev h0
  have d5 : 5 ∣ j := hd 5 h5 (by norm_num)
  have d2 : 2 ∣ j := by
    rcases hev with h | h | h | h
    · exact hd 2 h (by norm_num)
    · exact (dvd_trans (by norm_num) (hd 4 h (by norm_num)))
    · exact (dvd_trans (by norm_num) (hd 6 h (by norm_num)))
    · exact (dvd_trans (by norm_num) (hd 8 h (by norm_num)))
  have h10 : j % 10 = 0 := by omega
  have : (0 : ℕ) ∈ Nat.digits 10 j := by
    rw [Nat.digits_def' (by norm_num) hj, h10]; simp
  rw [← List.mem_toFinset, hT, List.mem_toFinset] at this
  exact h0 this

lemma part2 : ∀ n k : ℕ, 0 < n → IsLeast {j : ℕ | Valid n j} k → k ≤ B := by
  intro n k hn hk
  set T := (Nat.digits 10 n).toFinset with hTdef
  have hmem : T ∈ (Finset.range 10).powerset := by
    rw [Finset.mem_powerset]
    intro d hd
    rw [hTdef, List.mem_toFinset] at hd
    exact Finset.mem_range.2 (Nat.digits_lt_base (by norm_num) hd)
  have hlast : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 hn.ne'
  have hne0 := Nat.getLast_digit_ne_zero 10 hn.ne'
  rcases table_ok T hmem with h | h | h | h
  · exfalso
    have : (Nat.digits 10 n).getLast hlast ∈ T := by
      rw [hTdef, List.mem_toFinset]; exact List.getLast_mem _
    rw [h] at this; simp at this
  · exfalso
    have : (Nat.digits 10 n).getLast hlast ∈ T := by
      rw [hTdef, List.mem_toFinset]; exact List.getLast_mem _
    rw [h] at this; simp at this; exact hne0 this
  · exact (bad_false n k h hk.1).elim
  · obtain ⟨hw0, hwB, hwT, hwd⟩ := h
    set w := tbl.getD (maskOf T) 0
    have hlt : w < 10 ^ 13 := by unfold B at hwB; omega
    rw [digs_eq 13 w hlt] at hwT
    have hv : Valid n w := ⟨hw0, hwT, fun d hd hd0 =>
      Nat.dvd_of_mod_eq_zero (hwd d (by rw [hTdef, List.mem_toFinset]; exact hd) hd0)⟩
    exact le_trans (hk.2 hv) hwB

/-! part 1 -/

def gen : ℕ → ℕ → List (List ℕ)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, j => (gen n j).map (7 :: ·) ++
      (match j with
        | 0 => []
        | j' + 1 => (gen n j').map (0 :: ·) ++ (gen n j').map (9 :: ·))

lemma mem_gen : ∀ L : List ℕ, (∀ x ∈ L, x = 0 ∨ x = 7 ∨ x = 9) →
    L ∈ gen L.length (L.length - L.count 7) := by
  intro L
  induction L with
  | nil => intro _; simp [gen]
  | cons x L ih =>
    intro h
    have hL := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hc := List.count_le_length (a := 7) (l := L)
    rcases h x List.mem_cons_self with rfl | rfl | rfl
    · simp only [List.length_cons, List.count_cons, gen]
      rw [show L.length + 1 - (L.count 7 + if (0 == 7) = true then 1 else 0) = (L.length - L.count 7) + 1 by
        simp; omega]
      simp [hL]
    · simp only [List.length_cons, List.count_cons, beq_self_eq_true, if_true, gen]
      rw [show L.length + 1 - (L.count 7 + 1) = L.length - L.count 7 by omega]
      simp [hL]
    · simp only [List.length_cons, List.count_cons, gen]
      rw [show L.length + 1 - (L.count 7 + if (9 == 7) = true then 1 else 0) = (L.length - L.count 7) + 1 by
        simp; omega]
      simp [hL]

lemma sum_079 : ∀ L : List ℕ, (∀ x ∈ L, x = 0 ∨ x = 7 ∨ x = 9) →
    L.sum = 7 * L.count 7 + 9 * L.count 9 := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons x L ih =>
    intro h
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rcases h x List.mem_cons_self with rfl | rfl | rfl <;> simp [List.count_cons, this] <;> ring

def finalCheck (L : List ℕ) : Bool :=
  !(decide (Nat.ofDigits 10 L < B) && Nat.ofDigits 10 L % 63 == 0 && L.contains 0 && L.contains 9 &&
    L.getLast? != some 0)

set_option maxRecDepth 100000 in
lemma final_ok : ∀ L ∈ gen 9 0 ++ gen 10 1 ++ gen 11 2 ++ gen 12 3, finalCheck L = true := by
  decide +kernel

lemma part1_min : ∀ k, Valid 709 k → B ≤ k := by
  intro k hv
  by_contra hlt
  push Not at hlt
  obtain ⟨hk, hT, hd⟩ := hv
  have h709 : Nat.digits 10 709 = [9, 0, 7] := by norm_num
  rw [h709] at hT hd
  set L := Nat.digits 10 k with hL
  have hmemL : ∀ x ∈ L, x = 0 ∨ x = 7 ∨ x = 9 := by
    intro x hx
    rw [← List.mem_toFinset, hT] at hx; simp at hx; omega
  have h7 : 7 ∣ k := hd 7 (by simp) (by norm_num)
  have h9 : 9 ∣ k := hd 9 (by simp) (by norm_num)
  have hlen : L.length ≤ 12 := by
    rw [hL, Nat.digits_length_le_iff (by norm_num)]
    unfold B at hlt; norm_num; omega
  have hsum : 9 ∣ L.sum := (Nat.nine_dvd_iff k).1 h9
  rw [sum_079 L hmemL] at hsum
  have hc9 : 9 ∣ L.count 7 := by
    have : 9 ∣ 7 * L.count 7 := by
      have := (Nat.dvd_add_right (dvd_mul_right 9 (L.count 9))).1 (by rwa [add_comm] at hsum)
      exact this
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
  have hin7 : 7 ∈ L := by rw [← List.mem_toFinset, hT]; simp
  have hpos := List.count_pos_iff.2 hin7
  have hcle := List.count_le_length (a := 7) (l := L)
  have hc : L.count 7 = 9 := by omega
  have hg := mem_gen L hmemL
  rw [hc] at hg
  have hin : L ∈ gen 9 0 ++ gen 10 1 ++ gen 11 2 ++ gen 12 3 := by
    have : L.length = 9 ∨ L.length = 10 ∨ L.length = 11 ∨ L.length = 12 := by omega
    rcases this with h | h | h | h <;> rw [h] at hg <;> simp [hg]
  have hf := final_ok L hin
  have hof : Nat.ofDigits 10 L = k := Nat.ofDigits_digits 10 k
  have hne : L.getLast? ≠ some 0 := by
    have hk0 : k ≠ 0 := hk.ne'
    have hnn : L ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 hk0
    rw [List.getLast?_eq_getLast hnn]
    simpa using Nat.getLast_digit_ne_zero 10 hk0
  have h0 : 0 ∈ L := by rw [← List.mem_toFinset, hT]; simp
  have h9' : 9 ∈ L := by rw [← List.mem_toFinset, hT]; simp
  simp [finalCheck, hof, hlt, hne, h0, h9', List.contains_iff_mem] at hf
  omega

lemma part1_valid : Valid 709 B := by
  refine ⟨by norm_num [B], ?_, ?_⟩
  · rw [← digs_eq 13 B (by norm_num [B]), ← digs_eq 3 709 (by norm_num)]; decide
  · rw [← digs_eq 3 709 (by norm_num)]; decide

end OMA.Sol_oeis_a390761

theorem OMA.solution : type_of% @OMA.S_oeis_a390761.main :=
  ⟨⟨OMA.Sol_oeis_a390761.part1_valid, OMA.Sol_oeis_a390761.part1_min⟩,
    OMA.Sol_oeis_a390761.part2⟩
