import OMAStatements.S_oeis_a000720

/-!
# A000720 — Reduction of the Second Hardy–Littlewood Conjecture

Source: https://oeis.org/A000720

We unconditionally prove the Second Hardy–Littlewood inequality
`Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y` across two infinite/finite
regimes and reduce the full conjecture (`2 ≤ x`, `2 ≤ y`) to critical prime-sum boundary pairs,
which we split along the classical balanced vs. super-quadratic divide:

1. **Unconditional wheel-sieve + Jacobsthal theorem (`wheel_sieve_bound`, `min x y ≤ 216`)**:
   Verified for ALL `y ≥ 2` and `2 ≤ x ≤ 216` via a `2310`-wheel (`2 · 3 · 5 · 7 · 11`) combined
   with a `13`-rough composite witness from the Jacobsthal bound `j(2310) = 14`.
2. **Unconditional finite-box certificate (`box_bound`, `x + y ≤ 8000`)**:
   Verified for all `2 ≤ x`, `2 ≤ y` with `x + y ≤ 8000` via a bitmask Sieve of Eratosthenes up to
   `p_1007 = 8009`, binary-tree prime bitmask reconstruction, and SWAR 20-bit parallel lane checks
   certifying `p_m + p_n - 1 ≤ p_{m + n}` across all `1 ≤ m ≤ n` with `m + n ≤ 1007`.
3. **Symmetry, prime-sum, and boundary-shift reduction (`wlog_prime_sum_reduction`)**:
   Reduces arbitrary pairs `(x, y)` to critical pairs satisfying `216 < x`, `x ≤ y`, `8000 < x + y`,
   `Nat.Prime (x + y)`, and `Nat.Prime (x + 1) ∨ Nat.Prime y ∨ y ≤ x + 1`.
4. **Regime split (`H1` vs. `H2`)**:
   - `H1` (**Balanced / Udrescu 1975 regime**, `y ≤ x ^ 2`): `log y ≤ 2 log x`, where the Prime
     Number Theorem asymptotically forces `π(x + y) < π(x) + π(y)` (expected true and provable via
     explicit PNT bounds).
   - `H2` (**Skew / Hensley–Richards 1974 regime**, `x ^ 2 < y`): super-quadratic skew pairs,
     containing the regime `y ≫ exp(x / (log x)^2)` where admissible prime `k`-tuples govern the
     conjectured obstruction.
-/

namespace OMA.R_oeis_a000720_R1

/-!
Unconditional wheel-sieve bound (`X0 = 216`) and symmetry + prime-sum + boundary-shift
reductions for `oeis-a000720` (Second Hardy-Littlewood conjecture).
-/

private theorem prime_seven : Nat.Prime 7 := by
  refine Nat.prime_def_lt'.mpr ⟨by omega, fun m hm2 hmlt => ?_⟩
  have hm : m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 := by omega
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem prime_eleven : Nat.Prime 11 := by
  refine Nat.prime_def_lt'.mpr ⟨by omega, fun m hm2 hmlt => ?_⟩
  have hm : m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 := by omega
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem prime_thirteen : Nat.Prime 13 := by
  refine Nat.prime_def_lt'.mpr ⟨by omega, fun m hm2 hmlt => ?_⟩
  have hm : m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨
      m = 11 ∨ m = 12 := by omega
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem prime_iff_sieve_le_288 {n : ℕ} (hn : n ≤ 288) :
    Nat.Prime n ↔
      (n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13 ∨
        (2 ≤ n ∧ n % 2 ≠ 0 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0 ∧ n % 7 ≠ 0 ∧ n % 11 ≠ 0 ∧ n % 13 ≠ 0)) := by
  constructor
  · intro hp
    by_cases hsmall : n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 11 ∨ n = 13
    · rcases hsmall with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · right; right; right; right; right; right
      have h2 : 2 ≤ n := hp.two_le
      have hndvd : ∀ q : ℕ, 1 < q → q ≠ n → n % q ≠ 0 := by
        intro q hq1 hqn hmod
        rcases hp.eq_one_or_self_of_dvd _ (Nat.dvd_of_mod_eq_zero hmod) with rfl | rfl <;> omega
      refine ⟨h2, hndvd 2 (by omega) (by omega), hndvd 3 (by omega) (by omega),
        hndvd 5 (by omega) (by omega), hndvd 7 (by omega) (by omega),
        hndvd 11 (by omega) (by omega), hndvd 13 (by omega) (by omega)⟩
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h2, hm2, hm3, hm5, hm7, hm11, hm13⟩
    · exact Nat.prime_two
    · exact Nat.prime_three
    · exact Nat.prime_five
    · exact prime_seven
    · exact prime_eleven
    · exact prime_thirteen
    · by_contra hnp
      have hsq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
      have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
      have hge2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
      have hle16 : n.minFac ≤ 16 := by
        by_contra hgt
        have : 17 * 17 ≤ n.minFac * n.minFac := Nat.mul_le_mul (by omega) (by omega)
        rw [sq] at hsq
        omega
      have hcases : n.minFac = 2 ∨ n.minFac = 3 ∨ n.minFac = 4 ∨ n.minFac = 5 ∨ n.minFac = 6 ∨
          n.minFac = 7 ∨ n.minFac = 8 ∨ n.minFac = 9 ∨ n.minFac = 10 ∨ n.minFac = 11 ∨
          n.minFac = 12 ∨ n.minFac = 13 ∨ n.minFac = 14 ∨ n.minFac = 15 ∨ n.minFac = 16 := by
        omega
      rcases hcases with hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq | hq <;>
        rw [hq] at hdvd
      · exact hm2 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact hm3 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact hm2 (Nat.mod_eq_zero_of_dvd (dvd_trans (by omega : 2 ∣ 4) hdvd))
      · exact hm5 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact hm2 (Nat.mod_eq_zero_of_dvd (dvd_trans (by omega : 2 ∣ 6) hdvd))
      · exact hm7 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact hm2 (Nat.mod_eq_zero_of_dvd (dvd_trans (by omega : 2 ∣ 8) hdvd))
      · exact hm3 (Nat.mod_eq_zero_of_dvd (dvd_trans (by omega : 3 ∣ 9) hdvd))
      · exact hm2 (Nat.mod_eq_zero_of_dvd (dvd_trans (by omega : 2 ∣ 10) hdvd))
      · exact hm11 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact hm2 (Nat.mod_eq_zero_of_dvd (dvd_trans (by omega : 2 ∣ 12) hdvd))
      · exact hm13 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact hm2 (Nat.mod_eq_zero_of_dvd (dvd_trans (by omega : 2 ∣ 14) hdvd))
      · exact hm3 (Nat.mod_eq_zero_of_dvd (dvd_trans (by omega : 3 ∣ 15) hdvd))
      · exact hm2 (Nat.mod_eq_zero_of_dvd (dvd_trans (by omega : 2 ∣ 16) hdvd))

private theorem primeCounting_succ_eq (n : ℕ) :
    Nat.primeCounting (n + 1) =
      Nat.primeCounting n + if Nat.Prime (n + 1) then 1 else 0 := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
    Nat.primesLE_succ]
  split_ifs
  · exact Finset.card_insert_of_notMem (Nat.notMem_primesLE n)
  · rfl

private theorem primeCounting_succ_of_not_prime {n : ℕ} (h : ¬ Nat.Prime (n + 1)) :
    Nat.primeCounting (n + 1) = Nat.primeCounting n := by
  rw [primeCounting_succ_eq, if_neg h, add_zero]

private theorem primeCounting_sub_one_of_not_prime {n : ℕ} (hn : 1 ≤ n) (h : ¬ Nat.Prime n) :
    Nat.primeCounting n = Nat.primeCounting (n - 1) := by
  have h1 : n - 1 + 1 = n := by omega
  rw [← h1, primeCounting_succ_of_not_prime (h1.symm ▸ h)]
  simp

private theorem primeCounting_add_le_add_card_Ioc (x y : ℕ) :
    Nat.primeCounting (x + y) ≤
      Nat.primeCounting y + ((Finset.Ioc y (y + x)).filter Nat.Prime).card := by
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting]
  calc
    (Nat.primesLE (x + y)).card ≤
        (Nat.primesLE y ∪ (Finset.Ioc y (y + x)).filter Nat.Prime).card := by
      apply Finset.card_le_card
      intro p hp
      rw [Nat.mem_primesLE] at hp
      rw [Finset.mem_union, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
      by_cases hpy : p ≤ y
      · exact Or.inl ⟨hpy, hp.2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hp.2⟩
    _ ≤ (Nat.primesLE y).card + ((Finset.Ioc y (y + x)).filter Nat.Prime).card :=
      Finset.card_union_le _ _

private theorem mod_ne_zero_of_prime_gt {p q : ℕ} (hp : Nat.Prime p) (hq : 1 < q) (hqp : q < p) :
    p % q ≠ 0 := by
  intro h
  rcases hp.eq_one_or_self_of_dvd _ (Nat.dvd_of_mod_eq_zero h) with rfl | rfl <;> omega

private theorem mul_thirteen_mod_ne_zero {m q : ℕ} (hq : Nat.Prime q) (hq13 : ¬ q ∣ 13)
    (hm : m % q ≠ 0) : (13 * m) % q ≠ 0 := by
  intro h
  rcases hq.dvd_mul.mp (Nat.dvd_of_mod_eq_zero h) with h1 | h2
  · exact hq13 h1
  · exact hm (Nat.mod_eq_zero_of_dvd h2)

private theorem exists_jacobsthal_2310_bool :
    ((List.range' 0 2310).all (fun r =>
      (List.range' 0 14).any (fun j =>
        (r + j) % 2 != 0 && (r + j) % 3 != 0 && (r + j) % 5 != 0 &&
        (r + j) % 7 != 0 && (r + j) % 11 != 0))) = true := by
  decide +kernel

private theorem composite_witness_Ioc {x y : ℕ} (hy : 13 ≤ y) (hx : 182 ≤ x) :
    ∃ w ∈ Finset.Ioc y (y + x),
      ¬ Nat.Prime w ∧
      (w % 2 ≠ 0 ∧ w % 3 ≠ 0 ∧ w % 5 ≠ 0 ∧ w % 7 ≠ 0 ∧ w % 11 ≠ 0) := by
  have hr_lt : (y / 13 + 1) % 2310 < 2310 := Nat.mod_lt _ (by omega)
  have hall := exists_jacobsthal_2310_bool
  rw [List.all_eq_true] at hall
  have hr_any := hall ((y / 13 + 1) % 2310)
    (List.mem_range'.mpr ⟨(y / 13 + 1) % 2310, hr_lt, by omega⟩)
  rw [List.any_eq_true] at hr_any
  obtain ⟨j, hjMem, hjOk⟩ := hr_any
  rw [List.mem_range'] at hjMem
  obtain ⟨i, hi_lt, hi_eq⟩ := hjMem
  have hj_lt : j < 14 := by omega
  simp only [Bool.and_eq_true, bne_iff_ne] at hjOk
  obtain ⟨⟨⟨⟨hj2, hj3⟩, hj5⟩, hj7⟩, hj11⟩ := hjOk
  refine ⟨13 * (y / 13 + 1 + j), ?_, ?_, ?_⟩
  · rw [Finset.mem_Ioc]
    omega
  · intro hp
    have hdvd : 13 ∣ 13 * (y / 13 + 1 + j) := Nat.dvd_mul_right 13 _
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h2 <;> omega
  · have hmod : ∀ q : ℕ, q ∣ 2310 →
        (y / 13 + 1 + j) % q = ((y / 13 + 1) % 2310 + j) % q := by
      intro q hq
      symm
      rw [Nat.add_mod, Nat.mod_mod_of_dvd _ hq, ← Nat.add_mod]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact mul_thirteen_mod_ne_zero Nat.prime_two (by omega)
        (by rw [hmod 2 (by omega)]; exact hj2)
    · exact mul_thirteen_mod_ne_zero Nat.prime_three (by omega)
        (by rw [hmod 3 (by omega)]; exact hj3)
    · exact mul_thirteen_mod_ne_zero Nat.prime_five (by omega)
        (by rw [hmod 5 (by omega)]; exact hj5)
    · exact mul_thirteen_mod_ne_zero prime_seven (by omega)
        (by rw [hmod 7 (by omega)]; exact hj7)
    · exact mul_thirteen_mod_ne_zero prime_eleven (by omega)
        (by rw [hmod 11 (by omega)]; exact hj11)

private theorem card_Ioc_wheel_eq_range (x y : ℕ) :
    ((Finset.Ioc y (y + x)).filter
        (fun n => n % 2 ≠ 0 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0 ∧ n % 7 ≠ 0 ∧ n % 11 ≠ 0)).card =
      ((Finset.range x).filter
        (fun k => ((y + 1) % 2310 + k) % 2 ≠ 0 ∧ ((y + 1) % 2310 + k) % 3 ≠ 0 ∧
          ((y + 1) % 2310 + k) % 5 ≠ 0 ∧ ((y + 1) % 2310 + k) % 7 ≠ 0 ∧
          ((y + 1) % 2310 + k) % 11 ≠ 0)).card := by
  symm
  apply Finset.card_bij (fun k _ => y + 1 + k)
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    rw [Finset.mem_filter, Finset.mem_Ioc]
    have hmod : ∀ q : ℕ, q ∣ 2310 → (y + 1 + k) % q = ((y + 1) % 2310 + k) % q := by
      intro q hq
      symm
      rw [Nat.add_mod, Nat.mod_mod_of_dvd _ hq, ← Nat.add_mod]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [hmod 2 (by omega), hmod 3 (by omega), hmod 5 (by omega),
      hmod 7 (by omega), hmod 11 (by omega)]
    exact hk.2
  · intro k1 _ k2 _ h
    omega
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    refine ⟨n - (y + 1), ?_, by omega⟩
    rw [Finset.mem_filter, Finset.mem_range]
    have hmod : ∀ q : ℕ, q ∣ 2310 → ((y + 1) % 2310 + (n - (y + 1))) % q = n % q := by
      intro q hq
      rw [Nat.add_mod, Nat.mod_mod_of_dvd (y + 1) hq, ← Nat.add_mod,
        show y + 1 + (n - (y + 1)) = n by omega]
    refine ⟨by omega, ?_⟩
    rw [hmod 2 (by omega), hmod 3 (by omega), hmod 5 (by omega),
      hmod 7 (by omega), hmod 11 (by omega)]
    exact hn.2

private theorem card_Ioc_primes_le_wheel {x y : ℕ} (hy : 13 ≤ y) :
    ((Finset.Ioc y (y + x)).filter Nat.Prime).card ≤
      ((Finset.Ioc y (y + x)).filter
        (fun n => n % 2 ≠ 0 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0 ∧ n % 7 ≠ 0 ∧ n % 11 ≠ 0)).card := by
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
  refine ⟨hp.1, mod_ne_zero_of_prime_gt hp.2 (by omega) (by omega),
    mod_ne_zero_of_prime_gt hp.2 (by omega) (by omega),
    mod_ne_zero_of_prime_gt hp.2 (by omega) (by omega),
    mod_ne_zero_of_prime_gt hp.2 (by omega) (by omega),
    mod_ne_zero_of_prime_gt hp.2 (by omega) (by omega)⟩

private theorem card_Ioc_primes_add_one_le_wheel {x y : ℕ} (hy : 13 ≤ y) (hx : 182 ≤ x) :
    ((Finset.Ioc y (y + x)).filter Nat.Prime).card + 1 ≤
      ((Finset.Ioc y (y + x)).filter
        (fun n => n % 2 ≠ 0 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0 ∧ n % 7 ≠ 0 ∧ n % 11 ≠ 0)).card := by
  obtain ⟨w, hwIoc, hwnp, hwmod⟩ := composite_witness_Ioc hy hx
  have hnotMem : w ∉ (Finset.Ioc y (y + x)).filter Nat.Prime := by
    rw [Finset.mem_filter]
    exact fun h => hwnp h.2
  rw [← Finset.card_insert_of_notMem hnotMem]
  apply Finset.card_le_card
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp'
  · exact Finset.mem_filter.mpr ⟨hwIoc, hwmod⟩
  · rw [Finset.mem_filter, Finset.mem_Ioc] at hp' ⊢
    refine ⟨hp'.1, mod_ne_zero_of_prime_gt hp'.2 (by omega) (by omega),
      mod_ne_zero_of_prime_gt hp'.2 (by omega) (by omega),
      mod_ne_zero_of_prime_gt hp'.2 (by omega) (by omega),
      mod_ne_zero_of_prime_gt hp'.2 (by omega) (by omega),
      mod_ne_zero_of_prime_gt hp'.2 (by omega) (by omega)⟩

private theorem zipWith_all_decide_le {as bs : List ℕ} {c i : ℕ}
    (ha : i < as.length) (hb : i < bs.length)
    (h : (List.zipWith (fun a b => decide (b ≤ a + c)) as bs).all id = true) :
    (bs[i]?).getD 0 ≤ (as[i]?).getD 0 + c := by
  rw [List.all_eq_true] at h
  have hmem : decide (bs[i] ≤ as[i] + c) ∈
      List.zipWith (fun a b => decide (b ≤ a + c)) as bs := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [ha, hb], by simp⟩
  simpa [ha, hb] using of_decide_eq_true (h _ hmem)

private theorem zipWith_all_decide_eq {as bs : List ℕ} {i : ℕ}
    (ha : i < as.length) (hb : i < bs.length)
    (h : (List.zipWith (fun a b => decide (b = a)) as bs).all id = true) :
    (bs[i]?).getD 0 = (as[i]?).getD 0 := by
  rw [List.all_eq_true] at h
  have hmem : decide (bs[i] = as[i]) ∈
      List.zipWith (fun a b => decide (b = a)) as bs := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [ha, hb], by simp⟩
  simpa [ha, hb] using of_decide_eq_true (h _ hmem)

private theorem exists_pi_cert :
    ∃ (piTbl : List ℕ) (iv1 iv2 : List (ℕ × ℕ)),
      piTbl.length = 229 ∧
      (piTbl[0]?).getD 0 = 0 ∧
      (List.zipWith (fun a b => decide (b = a))
        (List.zipWith (fun n a => a +
            if (n + 1 == 2 || n + 1 == 3 || n + 1 == 5 || n + 1 == 7 ||
                n + 1 == 11 || n + 1 == 13 ||
                (2 <= n + 1 && (n + 1) % 2 != 0 && (n + 1) % 3 != 0 && (n + 1) % 5 != 0 &&
                  (n + 1) % 7 != 0 && (n + 1) % 11 != 0 && (n + 1) % 13 != 0))
            then 1 else 0)
          (List.range' 0 228) piTbl)
        (piTbl.drop 1)).all id = true ∧
      ((List.range' 2 11).all (fun y =>
        (List.zipWith (fun px pxy => decide (pxy ≤ px + (piTbl[y]?).getD 0))
          (piTbl.drop 2) (piTbl.drop (2 + y))).all id) = true) ∧
      iv1 = [(2, 1), (4, 2), (6, 3), (10, 4), (12, 5), (16, 6), (18, 7), (22, 8), (28, 9), (30, 10), (36, 11), (40, 12), (42, 13), (46, 14), (52, 15), (58, 16), (60, 17), (66, 18), (70, 19), (72, 20), (78, 21), (82, 22), (88, 23), (96, 24), (100, 25), (102, 26), (106, 27), (108, 28), (112, 29), (126, 30), (130, 31), (136, 32), (138, 33), (148, 34), (150, 35), (156, 36), (162, 37), (166, 38), (172, 39), (178, 40), (180, 41), (186, 42)] ∧
      iv2 = [(190, 43), (192, 44), (196, 45), (198, 46), (210, 47), (216, 48)] ∧
      ((List.range' 2 185).all (fun x =>
        iv1.any (fun rk =>
          decide (x ≤ rk.1 ∧ rk.1 ≤ 186 ∧ rk.2 = (piTbl[x]?).getD 0))) = true) ∧
      ((List.range' 187 30).all (fun x =>
        iv2.any (fun rk =>
          decide (x ≤ rk.1 ∧ rk.1 ≤ 216 ∧ rk.2 = (piTbl[x]?).getD 0 + 1))) = true) :=
  ⟨[
    0, 0, 1, 2, 2, 3, 3, 4, 4, 4, 4, 5, 5, 6, 6, 6, 6, 7, 7, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 10, 10, 11,
    11, 11, 11, 11, 11, 12, 12, 12, 12, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 16, 17, 17, 18, 18, 18,
    18, 18, 18, 19, 19, 19, 19, 20, 20, 21, 21, 21, 21, 21, 21, 22, 22, 22, 22, 23, 23, 23, 23, 23, 23, 24, 24, 24, 24, 24, 24, 24,
    24, 25, 25, 25, 25, 26, 26, 27, 27, 27, 27, 28, 28, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 31,
    31, 31, 31, 32, 32, 32, 32, 32, 32, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, 35, 35, 36, 36, 36, 36, 36, 36, 37, 37, 37,
    37, 37, 37, 38, 38, 38, 38, 39, 39, 39, 39, 39, 39, 40, 40, 40, 40, 40, 40, 41, 41, 42, 42, 42, 42, 42, 42, 42, 42, 42, 42, 43,
    43, 44, 44, 44, 44, 45, 45, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 46, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 47, 48,
    48, 48, 48, 49, 49],
   [(2, 1), (4, 2), (6, 3), (10, 4), (12, 5), (16, 6), (18, 7), (22, 8), (28, 9), (30, 10), (36, 11), (40, 12), (42, 13), (46, 14), (52, 15), (58, 16), (60, 17), (66, 18), (70, 19), (72, 20), (78, 21), (82, 22), (88, 23), (96, 24), (100, 25), (102, 26), (106, 27), (108, 28), (112, 29), (126, 30), (130, 31), (136, 32), (138, 33), (148, 34), (150, 35), (156, 36), (162, 37), (166, 38), (172, 39), (178, 40), (180, 41), (186, 42)],
   [(190, 43), (192, 44), (196, 45), (198, 46), (210, 47), (216, 48)],
   by decide +kernel⟩

set_option maxHeartbeats 800000 in
private theorem exists_wheel_cert :
    ∃ pref : List ℕ,
      let p := pref
      p.length = 2527 ∧
      (p[0]?).getD 0 = 0 ∧
      (List.zipWith (fun a b => decide (b = a))
        (List.zipWith (fun n a => a +
            if (n % 2 != 0 && n % 3 != 0 && n % 5 != 0 && n % 7 != 0 && n % 11 != 0)
            then 1 else 0)
          (List.range' 0 2526) p)
        (p.drop 1)).all id = true ∧
      ([(2, 1), (4, 2), (6, 3), (10, 4), (12, 5), (16, 6), (18, 7), (22, 8), (28, 9), (30, 10), (36, 11), (40, 12), (42, 13), (46, 14), (52, 15), (58, 16), (60, 17), (66, 18), (70, 19), (72, 20), (78, 21), (82, 22), (88, 23), (96, 24), (100, 25), (102, 26), (106, 27), (108, 28), (112, 29), (126, 30), (130, 31), (136, 32), (138, 33), (148, 34), (150, 35), (156, 36), (162, 37), (166, 38), (172, 39), (178, 40), (180, 41), (186, 42)].all (fun rk =>
        (List.zipWith (fun a b => decide (b ≤ a + rk.2)) p (p.drop rk.1)).all id) =
        true) ∧
      ([(190, 43), (192, 44), (196, 45), (198, 46), (210, 47), (216, 48)].all (fun rk =>
        (List.zipWith (fun a b => decide (b ≤ a + rk.2)) p (p.drop rk.1)).all id) =
        true) :=
  ⟨[
    0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 6, 6,
    7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 13, 13, 14, 14,
    14, 14, 14, 14, 15, 15, 15, 15, 16, 16, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 20,
    20, 20, 21, 21, 21, 21, 22, 22, 23, 23, 23, 23, 24, 24, 25, 25, 25, 25, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26,
    27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 31, 31, 32, 32, 32, 32, 32, 32, 33, 33,
    33, 33, 33, 33, 34, 34, 34, 34, 35, 35, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 38, 38, 39, 39, 39, 39, 39, 39, 39, 39, 39, 39,
    40, 40, 41, 41, 41, 41, 42, 42, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 43, 44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 45, 45,
    46, 46, 46, 46, 47, 47, 48, 48, 48, 48, 49, 49, 49, 49, 49, 49, 50, 50, 51, 51, 51, 51, 51, 51, 52, 52, 52, 52, 53, 53, 53, 53,
    53, 53, 54, 54, 54, 54, 54, 54, 55, 55, 55, 55, 55, 55, 56, 56, 57, 57, 57, 57, 57, 57, 58, 58, 58, 58, 59, 59, 60, 60, 60, 60,
    60, 60, 61, 61, 61, 61, 62, 62, 62, 62, 62, 62, 63, 63, 63, 63, 63, 63, 63, 63, 64, 64, 64, 64, 65, 65, 66, 66, 66, 66, 67, 67,
    67, 67, 67, 67, 68, 68, 68, 68, 68, 68, 68, 68, 69, 69, 69, 69, 69, 69, 70, 70, 70, 70, 70, 70, 70, 70, 70, 70, 71, 71, 72, 72,
    72, 72, 73, 73, 73, 73, 73, 73, 74, 74, 75, 75, 75, 75, 75, 75, 76, 76, 76, 76, 76, 76, 77, 77, 77, 77, 78, 78, 79, 79, 79, 79,
    80, 80, 80, 80, 80, 80, 81, 81, 82, 82, 82, 82, 82, 82, 83, 83, 83, 83, 84, 84, 85, 85, 85, 85, 85, 85, 86, 86, 86, 86, 86, 86,
    86, 86, 86, 86, 87, 87, 88, 88, 88, 88, 88, 88, 88, 88, 88, 88, 89, 89, 90, 90, 90, 90, 91, 91, 92, 92, 92, 92, 93, 93, 93, 93,
    93, 93, 94, 94, 94, 94, 94, 94, 94, 94, 95, 95, 95, 95, 96, 96, 97, 97, 97, 97, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98, 98,
    99, 99, 100, 100, 100, 100, 100, 100, 101, 101, 101, 101, 102, 102, 103, 103, 103, 103, 103, 103, 104, 104, 104, 104, 105, 105, 105, 105, 105, 105, 106, 106,
    106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 107, 107, 108, 108, 108, 108, 109, 109, 110, 110, 110, 110, 111, 111, 111, 111, 111, 111, 111, 111, 112, 112,
    112, 112, 112, 112, 113, 113, 113, 113, 114, 114, 114, 114, 114, 114, 115, 115, 116, 116, 116, 116, 117, 117, 117, 117, 117, 117, 118, 118, 119, 119, 119, 119,
    119, 119, 120, 120, 120, 120, 120, 120, 120, 120, 120, 120, 121, 121, 122, 122, 122, 122, 123, 123, 123, 123, 123, 123, 124, 124, 125, 125, 125, 125, 125, 125,
    126, 126, 126, 126, 127, 127, 128, 128, 128, 128, 129, 129, 130, 130, 130, 130, 130, 130, 130, 130, 130, 130, 131, 131, 132, 132, 132, 132, 132, 132, 132, 132,
    132, 132, 133, 133, 134, 134, 134, 134, 135, 135, 135, 135, 135, 135, 136, 136, 136, 136, 136, 136, 137, 137, 138, 138, 138, 138, 138, 138, 139, 139, 139, 139,
    139, 139, 140, 140, 140, 140, 141, 141, 141, 141, 141, 141, 142, 142, 142, 142, 142, 142, 143, 143, 144, 144, 144, 144, 144, 144, 145, 145, 145, 145, 146, 146,
    147, 147, 147, 147, 147, 147, 148, 148, 148, 148, 149, 149, 149, 149, 149, 149, 150, 150, 150, 150, 150, 150, 150, 150, 151, 151, 151, 151, 152, 152, 153, 153,
    153, 153, 153, 153, 154, 154, 154, 154, 155, 155, 155, 155, 155, 155, 155, 155, 156, 156, 156, 156, 156, 156, 157, 157, 157, 157, 158, 158, 158, 158, 158, 158,
    159, 159, 160, 160, 160, 160, 161, 161, 161, 161, 161, 161, 162, 162, 162, 162, 162, 162, 162, 162, 163, 163, 163, 163, 163, 163, 164, 164, 164, 164, 165, 165,
    166, 166, 166, 166, 166, 166, 166, 166, 166, 166, 167, 167, 168, 168, 168, 168, 168, 168, 169, 169, 169, 169, 170, 170, 171, 171, 171, 171, 172, 172, 173, 173,
    173, 173, 173, 173, 173, 173, 173, 173, 174, 174, 175, 175, 175, 175, 175, 175, 175, 175, 175, 175, 176, 176, 177, 177, 177, 177, 178, 178, 179, 179, 179, 179,
    180, 180, 180, 180, 180, 180, 180, 180, 181, 181, 181, 181, 181, 181, 182, 182, 182, 182, 183, 183, 184, 184, 184, 184, 185, 185, 185, 185, 185, 185, 186, 186,
    186, 186, 186, 186, 187, 187, 188, 188, 188, 188, 188, 188, 189, 189, 189, 189, 190, 190, 190, 190, 190, 190, 190, 190, 191, 191, 191, 191, 192, 192, 192, 192,
    192, 192, 193, 193, 193, 193, 193, 193, 193, 193, 194, 194, 194, 194, 195, 195, 196, 196, 196, 196, 197, 197, 198, 198, 198, 198, 199, 199, 199, 199, 199, 199,
    199, 199, 200, 200, 200, 200, 200, 200, 201, 201, 201, 201, 202, 202, 202, 202, 202, 202, 203, 203, 203, 203, 203, 203, 204, 204, 204, 204, 204, 204, 205, 205,
    206, 206, 206, 206, 206, 206, 207, 207, 207, 207, 207, 207, 208, 208, 208, 208, 209, 209, 210, 210, 210, 210, 211, 211, 211, 211, 211, 211, 212, 212, 213, 213,
    213, 213, 213, 213, 214, 214, 214, 214, 215, 215, 216, 216, 216, 216, 217, 217, 218, 218, 218, 218, 218, 218, 218, 218, 218, 218, 219, 219, 220, 220, 220, 220,
    220, 220, 220, 220, 220, 220, 221, 221, 222, 222, 222, 222, 222, 222, 223, 223, 223, 223, 224, 224, 224, 224, 224, 224, 225, 225, 226, 226, 226, 226, 226, 226,
    227, 227, 227, 227, 228, 228, 229, 229, 229, 229, 230, 230, 230, 230, 230, 230, 231, 231, 231, 231, 231, 231, 232, 232, 232, 232, 232, 232, 232, 232, 233, 233,
    233, 233, 234, 234, 235, 235, 235, 235, 235, 235, 236, 236, 236, 236, 236, 236, 236, 236, 236, 236, 237, 237, 237, 237, 237, 237, 237, 237, 238, 238, 238, 238,
    239, 239, 240, 240, 240, 240, 241, 241, 242, 242, 242, 242, 243, 243, 243, 243, 243, 243, 243, 243, 244, 244, 244, 244, 244, 244, 244, 244, 244, 244, 245, 245,
    245, 245, 245, 245, 246, 246, 247, 247, 247, 247, 248, 248, 248, 248, 248, 248, 248, 248, 249, 249, 249, 249, 249, 249, 250, 250, 250, 250, 250, 250, 251, 251,
    251, 251, 252, 252, 253, 253, 253, 253, 254, 254, 254, 254, 254, 254, 255, 255, 256, 256, 256, 256, 256, 256, 257, 257, 257, 257, 258, 258, 258, 258, 258, 258,
    259, 259, 260, 260, 260, 260, 260, 260, 260, 260, 260, 260, 261, 261, 262, 262, 262, 262, 262, 262, 262, 262, 262, 262, 263, 263, 264, 264, 264, 264, 265, 265,
    266, 266, 266, 266, 267, 267, 267, 267, 267, 267, 268, 268, 269, 269, 269, 269, 269, 269, 270, 270, 270, 270, 271, 271, 272, 272, 272, 272, 273, 273, 273, 273,
    273, 273, 274, 274, 274, 274, 274, 274, 275, 275, 276, 276, 276, 276, 276, 276, 277, 277, 277, 277, 277, 277, 278, 278, 278, 278, 278, 278, 279, 279, 279, 279,
    280, 280, 280, 280, 280, 280, 281, 281, 281, 281, 281, 281, 281, 281, 282, 282, 282, 282, 283, 283, 284, 284, 284, 284, 285, 285, 286, 286, 286, 286, 287, 287,
    287, 287, 287, 287, 287, 287, 288, 288, 288, 288, 288, 288, 289, 289, 289, 289, 290, 290, 290, 290, 290, 290, 290, 290, 291, 291, 291, 291, 292, 292, 292, 292,
    292, 292, 293, 293, 294, 294, 294, 294, 294, 294, 295, 295, 295, 295, 295, 295, 296, 296, 296, 296, 297, 297, 298, 298, 298, 298, 299, 299, 299, 299, 299, 299,
    300, 300, 300, 300, 300, 300, 300, 300, 301, 301, 301, 301, 302, 302, 303, 303, 303, 303, 304, 304, 305, 305, 305, 305, 305, 305, 305, 305, 305, 305, 306, 306,
    307, 307, 307, 307, 307, 307, 307, 307, 307, 307, 308, 308, 309, 309, 309, 309, 310, 310, 311, 311, 311, 311, 312, 312, 312, 312, 312, 312, 313, 313, 314, 314,
    314, 314, 314, 314, 314, 314, 314, 314, 315, 315, 316, 316, 316, 316, 317, 317, 317, 317, 317, 317, 318, 318, 318, 318, 318, 318, 318, 318, 319, 319, 319, 319,
    319, 319, 320, 320, 320, 320, 321, 321, 322, 322, 322, 322, 322, 322, 323, 323, 323, 323, 324, 324, 324, 324, 324, 324, 325, 325, 325, 325, 325, 325, 325, 325,
    326, 326, 326, 326, 327, 327, 327, 327, 327, 327, 328, 328, 329, 329, 329, 329, 330, 330, 330, 330, 330, 330, 330, 330, 331, 331, 331, 331, 331, 331, 332, 332,
    332, 332, 333, 333, 333, 333, 333, 333, 334, 334, 335, 335, 335, 335, 336, 336, 336, 336, 336, 336, 337, 337, 338, 338, 338, 338, 338, 338, 339, 339, 339, 339,
    339, 339, 340, 340, 340, 340, 341, 341, 341, 341, 341, 341, 342, 342, 342, 342, 342, 342, 343, 343, 344, 344, 344, 344, 344, 344, 345, 345, 345, 345, 345, 345,
    346, 346, 346, 346, 347, 347, 348, 348, 348, 348, 348, 348, 348, 348, 348, 348, 349, 349, 350, 350, 350, 350, 350, 350, 350, 350, 350, 350, 351, 351, 352, 352,
    352, 352, 353, 353, 354, 354, 354, 354, 355, 355, 355, 355, 355, 355, 356, 356, 357, 357, 357, 357, 357, 357, 358, 358, 358, 358, 359, 359, 360, 360, 360, 360,
    360, 360, 360, 360, 360, 360, 361, 361, 361, 361, 361, 361, 362, 362, 363, 363, 363, 363, 363, 363, 364, 364, 364, 364, 365, 365, 366, 366, 366, 366, 366, 366,
    367, 367, 367, 367, 368, 368, 368, 368, 368, 368, 369, 369, 369, 369, 369, 369, 369, 369, 370, 370, 370, 370, 371, 371, 372, 372, 372, 372, 373, 373, 374, 374,
    374, 374, 374, 374, 374, 374, 374, 374, 374, 374, 375, 375, 375, 375, 375, 375, 376, 376, 376, 376, 377, 377, 377, 377, 377, 377, 378, 378, 379, 379, 379, 379,
    380, 380, 380, 380, 380, 380, 381, 381, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 382, 383, 383, 383, 383, 384, 384, 385, 385, 385, 385, 386, 386,
    386, 386, 386, 386, 386, 386, 387, 387, 387, 387, 387, 387, 388, 388, 388, 388, 389, 389, 390, 390, 390, 390, 391, 391, 392, 392, 392, 392, 392, 392, 392, 392,
    392, 392, 393, 393, 394, 394, 394, 394, 394, 394, 394, 394, 394, 394, 395, 395, 395, 395, 395, 395, 396, 396, 397, 397, 397, 397, 398, 398, 398, 398, 398, 398,
    399, 399, 400, 400, 400, 400, 400, 400, 401, 401, 401, 401, 402, 402, 403, 403, 403, 403, 404, 404, 404, 404, 404, 404, 405, 405, 405, 405, 405, 405, 406, 406,
    407, 407, 407, 407, 407, 407, 408, 408, 408, 408, 409, 409, 410, 410, 410, 410, 410, 410, 410, 410, 410, 410, 411, 411, 411, 411, 411, 411, 412, 412, 412, 412,
    412, 412, 412, 412, 413, 413, 413, 413, 413, 413, 414, 414, 414, 414, 415, 415, 416, 416, 416, 416, 417, 417, 417, 417, 417, 417, 417, 417, 418, 418, 418, 418,
    418, 418, 419, 419, 419, 419, 420, 420, 420, 420, 420, 420, 421, 421, 422, 422, 422, 422, 423, 423, 423, 423, 423, 423, 424, 424, 425, 425, 425, 425, 425, 425,
    426, 426, 426, 426, 426, 426, 427, 427, 427, 427, 427, 427, 428, 428, 428, 428, 429, 429, 429, 429, 429, 429, 430, 430, 431, 431, 431, 431, 431, 431, 432, 432,
    432, 432, 433, 433, 434, 434, 434, 434, 435, 435, 436, 436, 436, 436, 436, 436, 436, 436, 436, 436, 437, 437, 437, 437, 437, 437, 437, 437, 437, 437, 437, 437,
    438, 438, 439, 439, 439, 439, 440, 440, 441, 441, 441, 441, 441, 441, 441, 441, 441, 441, 442, 442, 443, 443, 443, 443, 443, 443, 444, 444, 444, 444, 445, 445,
    446, 446, 446, 446, 447, 447, 447, 447, 447, 447, 448, 448, 448, 448, 448, 448, 449, 449, 450, 450, 450, 450, 450, 450, 450, 450, 450, 450, 451, 451, 452, 452,
    452, 452, 452, 452, 453, 453, 453, 453, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 454, 455, 455, 455, 455, 456, 456, 457, 457, 457, 457,
    458, 458, 459, 459, 459, 459, 460, 460, 460, 460, 460, 460, 460, 460, 461, 461, 461, 461, 461, 461, 462, 462, 462, 462, 463, 463, 463, 463, 463, 463, 464, 464,
    465, 465, 465, 465, 466, 466, 466, 466, 466, 466, 467, 467, 468, 468, 468, 468, 468, 468, 469, 469, 469, 469, 469, 469, 470, 470, 470, 470, 471, 471, 472, 472,
    472, 472, 473, 473, 473, 473, 473, 473, 474, 474, 475, 475, 475, 475, 475, 475, 476, 476, 476, 476, 477, 477, 478, 478, 478, 478, 479, 479, 479, 479, 479, 479,
    479, 479, 479, 479, 479, 479, 480, 480, 481, 481, 481, 481, 481, 481, 481, 481, 481, 481, 481, 481, 482, 482, 482, 482, 483, 483, 484, 484, 484, 484, 485, 485,
    485, 485, 485, 485, 486, 486, 487, 487, 487, 487, 487, 487, 488, 488, 488, 488, 489, 489, 490, 490, 490, 490, 491, 491, 491, 491, 491, 491, 492, 492, 492, 492,
    492, 492, 493, 493, 494, 494, 494, 494, 494, 494, 495, 495, 495, 495, 496, 496, 497, 497, 497, 497, 497, 497, 498, 498, 498, 498, 499, 499, 499, 499, 499, 499,
    500, 500, 500, 500, 500, 500, 500, 500, 501, 501, 501, 501, 502, 502, 503, 503, 503, 503, 504, 504, 505, 505, 505, 505, 506, 506, 506, 506, 506, 506, 506, 506,
    506, 506, 506, 506, 506, 506, 507, 507, 507, 507, 508, 508, 508, 508, 508, 508, 509, 509, 510, 510, 510, 510, 510, 510, 510, 510, 510, 510, 511, 511, 512, 512,
    512, 512, 512, 512, 513, 513, 513, 513, 513, 513, 514, 514, 514, 514, 515, 515, 516, 516, 516, 516, 517, 517, 517, 517, 517, 517, 518, 518, 519, 519, 519, 519,
    519, 519, 519, 519, 519, 519, 520, 520, 521, 521, 521, 521, 522, 522, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 523, 524, 524, 524, 524, 524], by decide +kernel⟩

/-- **Unconditional Wheel-Sieve + Jacobsthal Bound (`X0 = 216`)**:
`Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y` holds unconditionally for all
`2 ≤ x ≤ 216` and ALL `y ≥ 2`. -/
theorem wheel_sieve_bound :
    ∀ x y : ℕ, 2 ≤ x → x ≤ 216 → 2 ≤ y →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  obtain ⟨piTbl, iv1, iv2, hpiLen, hpi0, hpiStep, hpiSmallY,
    hiv1Eq, hiv2Eq, hcov1, hcov2⟩ := exists_pi_cert
  obtain ⟨pref, hprefLen, hpref0, hprefStep, hwheel1, hwheel2⟩ := exists_wheel_cert
  rw [← hiv1Eq] at hwheel1
  rw [← hiv2Eq] at hwheel2
  have hpiEq : ∀ n : ℕ, n ≤ 228 → (piTbl[n]?).getD 0 = Nat.primeCounting n := by
    intro n hn
    induction n with
    | zero => simpa using hpi0
    | succ m ih =>
      have hm : m < 228 := by omega
      have hmLen : m < piTbl.length := by omega
      have hm1Len : m + 1 < piTbl.length := by omega
      have hstep := zipWith_all_decide_eq (i := m)
        (by simp [hpiLen, hm]) (by simp [hpiLen, hm]) hpiStep
      simp only [List.getElem?_drop, show 1 + m = m + 1 by omega,
        List.getElem?_zipWith, List.getElem?_range', hm, zero_add, one_mul,
        List.getElem?_eq_getElem hmLen, List.getElem?_eq_getElem hm1Len,
        Option.getD_some] at hstep ih ⊢
      rw [hstep, ih (by omega), primeCounting_succ_eq]
      congr 1
      have hp_iff := prime_iff_sieve_le_288 (n := m + 1) (by omega)
      simp only [beq_iff_eq, bne_iff_ne, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      by_cases hp : Nat.Prime (m + 1)
      · rw [if_pos hp, if_pos]
        rcases hp_iff.mp hp with h | h | h | h | h | h | ⟨ha, hb, hc, hd, he, hf, hg⟩
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩, hg⟩
      · rw [if_neg hp, if_neg]
        intro h1
        apply hp
        rw [hp_iff]
        rcases h1 with (((((h | h) | h) | h) | h) | h) | ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩, hg⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, hb, hc, hd, he, hf, hg⟩)))))
  have hprefStepAt : ∀ n : ℕ, n < 2526 →
      (pref[n + 1]?).getD 0 = (pref[n]?).getD 0 +
        if (n % 2 ≠ 0 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0 ∧ n % 7 ≠ 0 ∧ n % 11 ≠ 0) then 1 else 0 := by
    intro n hn
    have hnLen : n < pref.length := by omega
    have hn1Len : n + 1 < pref.length := by omega
    have hstep := zipWith_all_decide_eq (i := n)
      (by simp [hprefLen, hn]) (by simp [hprefLen, hn]) hprefStep
    simp only [List.getElem?_drop, show 1 + n = n + 1 by omega,
      List.getElem?_zipWith, List.getElem?_range', hn, zero_add, one_mul,
      List.getElem?_eq_getElem hnLen, List.getElem?_eq_getElem hn1Len,
      Option.getD_some] at hstep ⊢
    rw [hstep]
    congr 1
    simp only [Bool.and_eq_true, bne_iff_ne]
    by_cases h : n % 2 ≠ 0 ∧ n % 3 ≠ 0 ∧ n % 5 ≠ 0 ∧ n % 7 ≠ 0 ∧ n % 11 ≠ 0
    · rw [if_pos h, if_pos ⟨⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2.1⟩, h.2.2.2.2⟩]
    · rw [if_neg h, if_neg (fun h1 => h ⟨h1.1.1.1.1, h1.1.1.1.2, h1.1.1.2, h1.1.2, h1.2⟩)]
  have hprefRange : ∀ r x : ℕ, r + x ≤ 2526 →
      ((Finset.range x).filter
          (fun k => (r + k) % 2 ≠ 0 ∧ (r + k) % 3 ≠ 0 ∧ (r + k) % 5 ≠ 0 ∧
            (r + k) % 7 ≠ 0 ∧ (r + k) % 11 ≠ 0)).card +
        (pref[r]?).getD 0 = (pref[r + x]?).getD 0 := by
    intro r x hrx
    induction x with
    | zero => simp
    | succ x ih =>
      rw [Finset.range_add_one, Finset.filter_insert, show r + (x + 1) = r + x + 1 by omega,
        hprefStepAt (r + x) (by omega), ← ih (by omega)]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (by simp)]
        omega
      · omega
  intro x y hx2 hx216 hy2
  by_cases hy12 : y ≤ 12
  · rw [List.all_eq_true] at hpiSmallY
    have hyMem : y ∈ List.range' 2 11 := List.mem_range'.mpr ⟨y - 2, by omega, by omega⟩
    have hyAll := hpiSmallY y hyMem
    have hle := zipWith_all_decide_le (i := x - 2)
      (by simp [hpiLen]; omega) (by simp [hpiLen]; omega) hyAll
    simp only [List.getElem?_drop] at hle
    rw [show 2 + (x - 2) = x by omega, show 2 + y + (x - 2) = x + y by omega] at hle
    rw [hpiEq (x + y) (by omega), hpiEq x (by omega), hpiEq y (by omega)] at hle
    exact hle
  · have hy13 : 13 ≤ y := by omega
    have hr_lt : (y + 1) % 2310 < 2310 := Nat.mod_lt _ (by omega)
    have hadd_le := primeCounting_add_le_add_card_Ioc x y
    by_cases hx186 : x ≤ 186
    · rw [List.all_eq_true] at hcov1 hwheel1
      have hxAny := hcov1 x (List.mem_range'.mpr ⟨x - 2, by omega, by omega⟩)
      rw [List.any_eq_true] at hxAny
      obtain ⟨rk, hrkMem, hrkDec⟩ := hxAny
      obtain ⟨hxr, hr186, hkEq⟩ := of_decide_eq_true hrkDec
      have hrkAll := hwheel1 rk hrkMem
      have hprefBound := zipWith_all_decide_le (i := (y + 1) % 2310)
        (by omega) (by simp [hprefLen]; omega) hrkAll
      simp only [List.getElem?_drop,
        show rk.1 + (y + 1) % 2310 = (y + 1) % 2310 + rk.1 by omega] at hprefBound
      rw [hkEq, hpiEq x (by omega),
        ← hprefRange ((y + 1) % 2310) rk.1 (by omega)] at hprefBound
      have hmono :
          ((Finset.range x).filter
            (fun k => ((y + 1) % 2310 + k) % 2 ≠ 0 ∧ ((y + 1) % 2310 + k) % 3 ≠ 0 ∧
              ((y + 1) % 2310 + k) % 5 ≠ 0 ∧ ((y + 1) % 2310 + k) % 7 ≠ 0 ∧
              ((y + 1) % 2310 + k) % 11 ≠ 0)).card ≤
          ((Finset.range rk.1).filter
            (fun k => ((y + 1) % 2310 + k) % 2 ≠ 0 ∧ ((y + 1) % 2310 + k) % 3 ≠ 0 ∧
              ((y + 1) % 2310 + k) % 5 ≠ 0 ∧ ((y + 1) % 2310 + k) % 7 ≠ 0 ∧
              ((y + 1) % 2310 + k) % 11 ≠ 0)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hxr))
      have hcard_le : ((Finset.Ioc y (y + x)).filter Nat.Prime).card ≤ Nat.primeCounting x := by
        calc
          ((Finset.Ioc y (y + x)).filter Nat.Prime).card ≤ _ := card_Ioc_primes_le_wheel hy13
          _ = _ := card_Ioc_wheel_eq_range x y
          _ ≤ Nat.primeCounting x := by omega
      omega
    · rw [List.all_eq_true] at hcov2 hwheel2
      have hxAny := hcov2 x (List.mem_range'.mpr ⟨x - 187, by omega, by omega⟩)
      rw [List.any_eq_true] at hxAny
      obtain ⟨rk, hrkMem, hrkDec⟩ := hxAny
      obtain ⟨hxr, hr216, hkEq⟩ := of_decide_eq_true hrkDec
      have hrkAll := hwheel2 rk hrkMem
      have hprefBound := zipWith_all_decide_le (i := (y + 1) % 2310)
        (by omega) (by simp [hprefLen]; omega) hrkAll
      simp only [List.getElem?_drop,
        show rk.1 + (y + 1) % 2310 = (y + 1) % 2310 + rk.1 by omega] at hprefBound
      rw [hkEq, hpiEq x (by omega),
        ← hprefRange ((y + 1) % 2310) rk.1 (by omega)] at hprefBound
      have hmono :
          ((Finset.range x).filter
            (fun k => ((y + 1) % 2310 + k) % 2 ≠ 0 ∧ ((y + 1) % 2310 + k) % 3 ≠ 0 ∧
              ((y + 1) % 2310 + k) % 5 ≠ 0 ∧ ((y + 1) % 2310 + k) % 7 ≠ 0 ∧
              ((y + 1) % 2310 + k) % 11 ≠ 0)).card ≤
          ((Finset.range rk.1).filter
            (fun k => ((y + 1) % 2310 + k) % 2 ≠ 0 ∧ ((y + 1) % 2310 + k) % 3 ≠ 0 ∧
              ((y + 1) % 2310 + k) % 5 ≠ 0 ∧ ((y + 1) % 2310 + k) % 7 ≠ 0 ∧
              ((y + 1) % 2310 + k) % 11 ≠ 0)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hxr))
      have hcard_le : ((Finset.Ioc y (y + x)).filter Nat.Prime).card + 1 ≤
          Nat.primeCounting x + 1 := by
        calc
          ((Finset.Ioc y (y + x)).filter Nat.Prime).card + 1 ≤ _ :=
            card_Ioc_primes_add_one_le_wheel hy13 (by omega)
          _ = _ := card_Ioc_wheel_eq_range x y
          _ ≤ Nat.primeCounting x + 1 := by omega
      omega

private theorem prime_sum_boundary_shift {S : ℕ}
    (hcrit : ∀ x y : ℕ, 216 < x → x ≤ y → x + y ≤ S → Nat.Prime (x + y) →
      (Nat.Prime (x + 1) ∨ y ≤ x + 1) →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y) :
    ∀ k x y : ℕ, 2 ≤ x → x ≤ y → y ≤ k → x + y ≤ S → Nat.Prime (x + y) →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  intro k
  induction k with
  | zero =>
    intro x y hx hxy hyk _ _
    omega
  | succ k ih =>
    intro x y hx hxy hyk hS hps
    by_cases hy_le : y ≤ k
    · exact ih x y hx hxy hy_le hS hps
    · by_cases hx216 : x ≤ 216
      · exact wheel_sieve_bound x y hx hx216 (by omega)
      · by_cases hb : Nat.Prime (x + 1) ∨ y ≤ x + 1
        · exact hcrit x y (by omega) hxy hS hps hb
        · have hnpx1 : ¬ Nat.Prime (x + 1) := fun h => hb (Or.inl h)
          have hxy1 : x + 1 < y := by omega
          have hsum_eq : (x + 1) + (y - 1) = x + y := by omega
          have hstep := ih (x + 1) (y - 1) (by omega) (by omega) (by omega)
            (by omega) (hsum_eq.symm ▸ hps)
          rw [hsum_eq, primeCounting_succ_of_not_prime hnpx1] at hstep
          have hmono := Nat.monotone_primeCounting (show y - 1 ≤ y by omega)
          omega

/-- **Bounded Sum Reduction (`wlog_prime_sum_reduction_upto`)**:
Reduces `Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y` for `x + y ≤ S`
to critical pairs with `216 < x ≤ y`, `Nat.Prime (x + y)`, and `Nat.Prime (x + 1) ∨ y ≤ x + 1`. -/
theorem wlog_prime_sum_reduction_upto (S : ℕ)
    (hcrit : ∀ x y : ℕ, 216 < x → x ≤ y → x + y ≤ S → Nat.Prime (x + y) →
      (Nat.Prime (x + 1) ∨ y ≤ x + 1) →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y) :
    ∀ x y : ℕ, 2 ≤ x → 2 ≤ y → x + y ≤ S →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  induction S with
  | zero =>
    intro x y hx _ hS
    omega
  | succ S ih =>
    intro x y hx hy hS
    by_cases hle : x + y ≤ S
    · exact ih (fun u v hu huv huS hp hb => hcrit u v hu huv (by omega) hp hb) x y hx hy hle
    · have hsum : x + y = S + 1 := by omega
      suffices hord : ∀ u v : ℕ, 2 ≤ u → u ≤ v → u + v = S + 1 →
          Nat.primeCounting (u + v) ≤ Nat.primeCounting u + Nat.primeCounting v by
        by_cases hxy : x ≤ y
        · exact hord x y hx hxy hsum
        · have h := hord y x hy (by omega) (by omega)
          rwa [add_comm y x, add_comm (Nat.primeCounting y)] at h
      intro u v hu huv huv_sum
      by_cases hu216 : u ≤ 216
      · exact wheel_sieve_bound u v hu hu216 (by omega)
      · by_cases hp : Nat.Prime (u + v)
        · exact prime_sum_boundary_shift hcrit v u v hu huv le_rfl (by omega) hp
        · have hsub := primeCounting_sub_one_of_not_prime (n := u + v) (by omega) hp
          have heq : u + v - 1 = u + (v - 1) := by omega
          rw [heq] at hsub
          have hprev := ih (fun a b ha hab haS hpa hba => hcrit a b ha hab (by omega) hpa hba)
            u (v - 1) hu (by omega) (by omega)
          have hmono := Nat.monotone_primeCounting (show v - 1 ≤ v by omega)
          omega

/-- **Strong Symmetry + Prime-Sum + Boundary-Shift Reduction (`wlog_prime_sum_reduction_strong`)**:
Requires only `Nat.Prime (x + 1) ∨ y ≤ x + 1` (since monotonicity of `Nat.primeCounting` allows
shifting `(x, y) ↦ (x + 1, y - 1)` whenever `¬ Nat.Prime (x + 1)` and `x + 1 < y`). -/
theorem wlog_prime_sum_reduction_strong (B : ℕ)
    (hbox : ∀ x y : ℕ, 2 ≤ x → 2 ≤ y → x + y ≤ B →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y)
    (hcrit : ∀ x y : ℕ, 216 < x → x ≤ y → B < x + y → Nat.Prime (x + y) →
      (Nat.Prime (x + 1) ∨ y ≤ x + 1) →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y) :
    ∀ x y : ℕ, 2 ≤ x → 2 ≤ y →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  intro x y hx hy
  apply wlog_prime_sum_reduction_upto (x + y) _ x y hx hy le_rfl
  intro u v hu huv _ hp hb
  by_cases hB : u + v ≤ B
  · exact hbox u v (by omega) (by omega) hB
  · exact hcrit u v hu huv (by omega) hp hb

/-- **Symmetry + Prime-Sum + Boundary-Shift Reduction (`wlog_prime_sum_reduction`)**:
Unconditionally reduces `oeis-a000720` (given `hbox` for `x + y ≤ B`) to pairs `(x, y)` satisfying
`216 < x`, `x ≤ y`, `B < x + y`, `Nat.Prime (x + y)`, and
`Nat.Prime (x + 1) ∨ Nat.Prime y ∨ y ≤ x + 1`. -/
theorem wlog_prime_sum_reduction (B : ℕ)
    (hbox : ∀ x y : ℕ, 2 ≤ x → 2 ≤ y → x + y ≤ B →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y)
    (hcrit : ∀ x y : ℕ, 216 < x → x ≤ y → B < x + y → Nat.Prime (x + y) →
      (Nat.Prime (x + 1) ∨ Nat.Prime y ∨ y ≤ x + 1) →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y) :
    ∀ x y : ℕ, 2 ≤ x → 2 ≤ y →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  refine wlog_prime_sum_reduction_strong B hbox (fun x y hx hxy hB hp hb => ?_)
  exact hcrit x y hx hxy hB hp (hb.elim Or.inl (fun h => Or.inr (Or.inr h)))

/-!
# Finite-box certificate for OEIS A000720 (`x + y ≤ 8000`)

Proves `Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y` unconditionally
for all `x, y ≥ 2` with `x + y ≤ 8000` via:
1. Bitmask Sieve of Eratosthenes certifying all primes up to `8009` (`= p_1007 > 8000`).
2. Binary-tree bitmask reconstruction and SWAR monotonicity certifying the packed 20-bit table `P`
   of the first `1008` primes `p_0 = 2 < p_1 = 3 < ... < p_1007 = 8009`.
3. SWAR parallel lane subtraction verifying `p_m + p_n - 1 ≤ p_(m + n)` for all `1 ≤ m ≤ n`
   with `m + n ≤ 1007`.
-/

-- 1. Bitmask Sieve of Eratosthenes lemmas

private lemma box_mq_above {q : ℕ} (hq : 0 < q) :
    ∀ r j : ℕ, (q <<< r) ≤ j →
      (Nat.rec (motive := fun _ => ℕ) 1 (fun k m => m ||| (m <<< (q <<< k))) r).testBit j = false := by
  intro r
  induction r with
  | zero =>
    intro j hj
    simp only [Nat.shiftLeft_zero] at hj
    rcases j with _ | j
    · omega
    · exact Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))
  | succ r ih =>
    intro j hj
    set m := Nat.rec (motive := fun _ => ℕ) 1 (fun k m => m ||| (m <<< (q <<< k))) r
    change (m ||| (m <<< (q <<< r))).testBit j = false
    rw [Nat.testBit_lor, Bool.or_eq_false_iff]
    have hL : (q <<< (r + 1)) = 2 * (q <<< r) := by
      simp [Nat.shiftLeft_eq, Nat.pow_succ]; ring
    have hj1 : (q <<< r) ≤ j := by omega
    have hj2 : (q <<< r) ≤ j - (q <<< r) := by omega
    refine ⟨ih j hj1, ?_⟩
    rw [Nat.testBit_shiftLeft]
    simp only [Bool.and_eq_false_imp]
    intro _
    exact ih (j - (q <<< r)) hj2

private lemma box_mq_below {q : ℕ} (hq : 0 < q) :
    ∀ r j : ℕ, j < (q <<< r) →
      ((Nat.rec (motive := fun _ => ℕ) 1 (fun k m => m ||| (m <<< (q <<< k))) r).testBit j = true ↔
        q ∣ j) := by
  intro r
  induction r with
  | zero =>
    intro j hj
    simp only [Nat.shiftLeft_zero] at hj
    change (1 : ℕ).testBit j = true ↔ q ∣ j
    rcases j with _ | j
    · simp
    · rw [Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow (by omega))]
      simp only [Bool.false_eq_true, false_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  | succ r ih =>
    intro j hj
    set m := Nat.rec (motive := fun _ => ℕ) 1 (fun k m => m ||| (m <<< (q <<< k))) r
    change (m ||| (m <<< (q <<< r))).testBit j = true ↔ q ∣ j
    have hL : (q <<< (r + 1)) = 2 * (q <<< r) := by
      simp [Nat.shiftLeft_eq, Nat.pow_succ]; ring
    have hdvdL : q ∣ (q <<< r) := by
      rw [Nat.shiftLeft_eq]
      exact dvd_mul_right q (2 ^ r)
    by_cases hlt : j < (q <<< r)
    · rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
      have hnot : ¬ ((q <<< r) ≤ j) := by omega
      simp [hnot, ih j hlt]
    · have hge : (q <<< r) ≤ j := by omega
      have hsub : j - (q <<< r) < (q <<< r) := by omega
      rw [Nat.testBit_lor, box_mq_above hq r j hge, Bool.false_or, Nat.testBit_shiftLeft]
      simp only [hge, decide_true, Bool.true_and, ih (j - (q <<< r)) hsub]
      constructor
      · intro hd
        have hsum := dvd_add hdvdL hd
        rwa [Nat.add_sub_of_le hge] at hsum
      · intro hd
        exact Nat.dvd_sub hd hdvdL

private lemma box_fold_or_testBit {r : ℕ} (ps : List ℕ) (acc j : ℕ) :
    (ps.foldl
      (fun a q =>
        a ||| (((Nat.rec (motive := fun _ => ℕ) 1 (fun k m => m ||| (m <<< (q <<< k))) r) >>> (2 * q)) <<< (2 * q)))
      acc).testBit j = true ↔
      acc.testBit j = true ∨
      ∃ q ∈ ps,
        (((Nat.rec (motive := fun _ => ℕ) 1 (fun k m => m ||| (m <<< (q <<< k))) r) >>> (2 * q)) <<< (2 * q)).testBit j = true := by
  induction ps generalizing acc with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih, Nat.testBit_lor, Bool.or_eq_true]
    constructor
    · rintro ((hacc | hq) | ⟨q', hq', hbit⟩)
      · exact Or.inl hacc
      · exact Or.inr ⟨q, Or.inl rfl, hq⟩
      · exact Or.inr ⟨q', Or.inr hq', hbit⟩
    · rintro (hacc | ⟨q', rfl | hq', hbit⟩)
      · exact Or.inl (Or.inl hacc)
      · exact Or.inl (Or.inr hbit)
      · exact Or.inr ⟨q', hq', hbit⟩

private lemma box_maskN_iff (n j : ℕ) (hn : 2 ≤ n) :
    (((1 <<< (n - 1)) - 1) <<< 2).testBit j = true ↔ (2 ≤ j ∧ j ≤ n) := by
  have h1 : (1 <<< (n - 1)) = 2 ^ (n - 1) := by simp [Nat.shiftLeft_eq]
  rw [h1, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

private lemma box_small_prime : ∀ q ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89] : List ℕ), Nat.Prime q := by
  decide +kernel

private lemma box_small_complete :
    ∀ q : Fin 90, Nat.Prime q.val → q.val ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89] : List ℕ) := by
  decide +kernel

private lemma box_primeMask_iff (j : ℕ) :
    ((((1 <<< (8009 - 1)) - 1) <<< 2) ^^^
      ((((1 <<< (8009 - 1)) - 1) <<< 2) &&&
        List.foldl
          (fun acc q =>
            acc ||| (((Nat.rec (motive := fun _ => ℕ) 1 (fun k m => m ||| (m <<< (q <<< k))) 13) >>> (2 * q)) <<< (2 * q)))
          0 ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89] : List ℕ))).testBit j = true ↔
      (j ≤ 8009 ∧ Nat.Prime j) := by
  set compMask := List.foldl
    (fun acc q =>
      acc ||| (((Nat.rec (motive := fun _ => ℕ) 1 (fun k m => m ||| (m <<< (q <<< k))) 13) >>> (2 * q)) <<< (2 * q)))
    0 ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89] : List ℕ)
  set maskN := ((1 <<< (8009 - 1)) - 1) <<< 2
  have hxor : (maskN ^^^ (maskN &&& compMask)).testBit j = (maskN.testBit j && !compMask.testBit j) := by
    rw [Nat.testBit_xor, Nat.testBit_land]
    cases maskN.testBit j <;> cases compMask.testBit j <;> rfl
  have hmaskN : maskN.testBit j = true ↔ (2 ≤ j ∧ j ≤ 8009) :=
    box_maskN_iff 8009 j (by decide)
  have hcomp : ∀ (hj : j ≤ 8009),
      compMask.testBit j = true ↔ ∃ q ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89] : List ℕ), 2 * q ≤ j ∧ q ∣ j := by
    intro hj
    rw [box_fold_or_testBit]
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨q, hqmem, hbit⟩
      have hqp : Nat.Prime q := box_small_prime q hqmem
      have hqpos : 0 < q := hqp.pos
      rw [Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Bool.and_eq_true, decide_eq_true_eq] at hbit
      obtain ⟨h2q, hbit⟩ := hbit
      rw [Nat.add_sub_of_le h2q] at hbit
      have hjlt : j < (q <<< 13) := by
        rw [Nat.shiftLeft_eq]
        have hR : 8009 < 2 ^ 13 := by decide
        have hq1 : 1 ≤ q := hqp.one_le
        nlinarith
      exact ⟨q, hqmem, h2q, (box_mq_below hqpos 13 j hjlt).mp hbit⟩
    · rintro ⟨q, hqmem, h2q, hdvd⟩
      have hqp : Nat.Prime q := box_small_prime q hqmem
      have hqpos : 0 < q := hqp.pos
      have hjlt : j < (q <<< 13) := by
        rw [Nat.shiftLeft_eq]
        have hR : 8009 < 2 ^ 13 := by decide
        have hq1 : 1 ≤ q := hqp.one_le
        nlinarith
      refine ⟨q, hqmem, ?_⟩
      rw [Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Bool.and_eq_true, decide_eq_true_eq]
      rw [Nat.add_sub_of_le h2q]
      exact ⟨h2q, (box_mq_below hqpos 13 j hjlt).mpr hdvd⟩
  rw [hxor, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, hmaskN]
  constructor
  · rintro ⟨⟨hj2, hjN⟩, hnotc⟩
    rw [hcomp hjN] at hnotc
    refine ⟨hjN, ?_⟩
    by_contra hnp
    have hqp : j.minFac.Prime := Nat.minFac_prime (by omega)
    have hdvd : j.minFac ∣ j := Nat.minFac_dvd j
    have hsq : j.minFac * j.minFac ≤ j := by
      simpa [sq] using Nat.minFac_sq_le_self (by omega) hnp
    have hlt_sq : j.minFac < 90 := by nlinarith
    have hmem : j.minFac ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89] : List ℕ) :=
      box_small_complete ⟨j.minFac, hlt_sq⟩ hqp
    have h2q : 2 * j.minFac ≤ j := by
      have := hqp.two_le
      nlinarith
    exact hnotc ⟨j.minFac, hmem, h2q, hdvd⟩
  · rintro ⟨hjN, hjp⟩
    refine ⟨⟨hjp.two_le, hjN⟩, ?_⟩
    rw [hcomp hjN]
    rintro ⟨q, hqmem, h2q, hdvd⟩
    have hqp : Nat.Prime q := box_small_prime q hqmem
    have heq : q = j := (Nat.prime_dvd_prime_iff_eq hqp hjp).mp hdvd
    have := hqp.two_le
    omega

-- 2. Binary-tree prime bitmask reconstruction lemma

private lemma box_tree_testBit :
    ∀ (d P j : ℕ),
      (Nat.rec (motive := fun _ => ℕ → ℕ)
        (fun X => 1 <<< (X &&& 0xFFFFF))
        (fun k rec X => rec X ||| rec (X >>> (20 <<< k)))
        d P).testBit j = true ↔
      ∃ k < (1 <<< d), ((P >>> (20 * k)) &&& 0xFFFFF) = j := by
  intro d
  induction d with
  | zero =>
    intro P j
    change (1 <<< (P &&& 0xFFFFF)).testBit j = true ↔ ∃ k < 1, ((P >>> (20 * k)) &&& 0xFFFFF) = j
    rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨0, by omega, by simpa using h⟩
    · rintro ⟨k, hk, h⟩
      have hk0 : k = 0 := by omega
      subst hk0
      simpa using h
  | succ d ih =>
    intro P j
    set rec := Nat.rec (motive := fun _ => ℕ → ℕ)
      (fun X => 1 <<< (X &&& 0xFFFFF))
      (fun k rec X => rec X ||| rec (X >>> (20 <<< k))) d
    change (rec P ||| rec (P >>> (20 <<< d))).testBit j = true ↔
      ∃ k < (1 <<< (d + 1)), ((P >>> (20 * k)) &&& 0xFFFFF) = j
    rw [Nat.testBit_lor, Bool.or_eq_true, ih P j, ih (P >>> (20 <<< d)) j]
    have hd2 : (1 <<< (d + 1)) = 2 * (1 <<< d) := by
      simp [Nat.shiftLeft_eq, Nat.pow_succ]; ring
    have h20 : (20 <<< d) = 20 * (1 <<< d) := by
      simp [Nat.shiftLeft_eq]
    constructor
    · rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩)
      · exact ⟨k, by omega, h⟩
      · refine ⟨(1 <<< d) + k, by omega, ?_⟩
        rw [← Nat.shiftRight_add, h20] at h
        have heq : 20 * (1 <<< d) + 20 * k = 20 * ((1 <<< d) + k) := by ring
        rw [heq] at h
        exact h
    · rintro ⟨k, hk, h⟩
      by_cases hlt : k < (1 <<< d)
      · exact Or.inl ⟨k, hlt, h⟩
      · refine Or.inr ⟨k - (1 <<< d), by omega, ?_⟩
        rw [← Nat.shiftRight_add, h20]
        have heq : 20 * (1 <<< d) + 20 * (k - (1 <<< d)) = 20 * k := by omega
        rw [heq]
        exact h

-- 3. SWAR 20-bit lane arithmetic lemmas

private lemma box_lt18_of_bits {X : ℕ}
    (h18 : X.testBit 18 = false) (h19 : X.testBit 19 = false) :
    X % (2 ^ 20) < 2 ^ 18 := by
  have h18' : (X / 262144) % 2 = 0 := by
    simpa [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two] using h18
  have h19' : (X / 524288) % 2 = 0 := by
    simpa [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two] using h19
  have hmod : X % (2 ^ 20) = X % 1048576 := rfl
  have hp18 : (2 ^ 18 : ℕ) = 262144 := rfl
  rw [hmod, hp18]
  omega

private lemma box_and_mask_lt (X n : ℕ) :
    (X &&& ((1 <<< n) - 1)) < 2 ^ n := by
  have h1 : (1 <<< n) = 2 ^ n := by rw [Nat.shiftLeft_eq, one_mul]
  rw [h1, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt X (Nat.two_pow_pos n)

private lemma box_sub_lane (X a cnt k : ℕ) (hk : k < cnt) :
    ((((X >>> (20 * a)) &&& ((1 <<< (20 * cnt)) - 1)) >>> (20 * k)) % (2 ^ 20)) =
      ((X >>> (20 * (a + k))) &&& 0xFFFFF) := by
  have hp20 : (0xFFFFF : ℕ) = 2 ^ 20 - 1 := by decide
  rw [hp20, Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 20
  · rw [← Nat.and_two_pow_sub_one_eq_mod, ← Nat.and_two_pow_sub_one_eq_mod]
    simp only [Nat.testBit_land, Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.and_true,
      Nat.testBit_shiftRight, Nat.shiftLeft_eq, one_mul]
    have hlt_bit : 20 * k + i < 20 * cnt := by omega
    have heq : 20 * a + (20 * k + i) = 20 * (a + k) + i := by ring
    simp [hlt_bit, heq]
  · have h1 : (((((X >>> (20 * a)) &&& ((1 <<< (20 * cnt)) - 1)) >>> (20 * k)) % (2 ^ 20))) < 2 ^ i :=
      (Nat.mod_lt _ (by decide)).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : ((X >>> (20 * (a + k))) % (2 ^ 20)) < 2 ^ i :=
      (Nat.mod_lt _ (by decide)).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_eq_false_of_lt h1, Nat.testBit_eq_false_of_lt h2]

private lemma box_ones_eq_of_mul :
    ∀ (m O : ℕ), O * 0xFFFFF = (1 <<< (20 * m)) - 1 →
      O = Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m := by
  intro m
  have hrec : ∀ n : ℕ, (Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) n) * 1048575 =
      2 ^ (20 * n) - 1 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      set u := Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) n
      change (1 + (u <<< 20)) * 1048575 = 2 ^ (20 * (n + 1)) - 1
      have hp2 : 2 ^ (20 * (n + 1)) = (2 ^ (20 * n)) * 1048576 := by
        rw [show 20 * (n + 1) = 20 * n + 20 by ring, Nat.pow_add]
      have hS : 2 ^ (20 * n) = (2 ^ (20 * n) - 1) + 1 :=
        (Nat.sub_add_cancel Nat.one_le_two_pow).symm
      set k := 2 ^ (20 * n) - 1
      rw [hp2, hS, Nat.shiftLeft_eq, show (2 ^ 20 : ℕ) = 1048576 from rfl]
      have hlhs : (1 + u * 1048576) * 1048575 = 1048575 + (u * 1048575) * 1048576 := by ring
      have hrhs : (k + 1) * 1048576 = (1048575 + k * 1048576) + 1 := by ring
      rw [hlhs, ih, hrhs, Nat.add_sub_cancel]
  intro O hO
  have hp1 : (1 <<< (20 * m)) = 2 ^ (20 * m) := by rw [Nat.shiftLeft_eq, one_mul]
  have hf : (0xFFFFF : ℕ) = 1048575 := rfl
  rw [hp1, hf, ← hrec m] at hO
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 1048575) hO

private lemma box_ones_shift :
    ∀ (r m : ℕ), r ≤ m →
      (Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m) >>> (20 * r) =
      Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) (m - r) := by
  intro r
  induction r with
  | zero =>
    intro m _
    simp
  | succ r ih =>
    intro m hm
    rcases m with _ | m
    · omega
    · have hstep :
          ((1 + ((Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m) <<< 20)) >>> 20) =
          Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m := by
        simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
        omega
      have hmul : 20 * (r + 1) = 20 + 20 * r := by ring
      change (1 + ((Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m) <<< 20)) >>> (20 * (r + 1)) = _
      rw [hmul, Nat.shiftRight_add, hstep, Nat.succ_sub_succ_eq_sub]
      exact ih m (by omega)

private lemma box_ones_lt (m : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m < 2 ^ (20 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    change 1 + ((Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m) <<< 20) < 2 ^ (20 * (m + 1))
    have hpow : 2 ^ (20 * (m + 1)) = (2 ^ (20 * m)) * (2 ^ 20) := by
      rw [← Nat.pow_add]; ring_nf
    rw [Nat.shiftLeft_eq, hpow]
    omega

private lemma box_mul_ones_lt {c m : ℕ} (hc : c < 2 ^ 20) :
    c * Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m < 2 ^ (20 * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    set u := Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m
    change c * (1 + (u <<< 20)) < 2 ^ (20 * (m + 1))
    have hpow : 2 ^ (20 * (m + 1)) = (2 ^ (20 * m)) * (2 ^ 20) := by
      rw [← Nat.pow_add]; ring_nf
    rw [Nat.shiftLeft_eq, hpow]
    have hc1 : c + 1 ≤ 2 ^ 20 := hc
    have hu1 : u + 1 ≤ 2 ^ (20 * m) := box_ones_lt m
    nlinarith

private lemma box_mul_ones_lane {c : ℕ} (hc : c < 2 ^ 20) :
    ∀ (t m : ℕ), t < m →
      (((c * Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m) >>> (20 * t)) % (2 ^ 20)) = c := by
  intro t
  induction t with
  | zero =>
    intro m hm
    rcases m with _ | m
    · omega
    · set u := Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m
      change ((c * (1 + (u <<< 20))) >>> 0) % (2 ^ 20) = c
      simp only [Nat.shiftRight_zero, Nat.shiftLeft_eq]
      have heq : c * (1 + u * 2 ^ 20) = c + (c * u) * 2 ^ 20 := by ring
      rw [heq]
      omega
  | succ t ih =>
    intro m hm
    rcases m with _ | m
    · omega
    · set u := Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) m
      change ((c * (1 + (u <<< 20))) >>> (20 * (t + 1))) % (2 ^ 20) = c
      have hmul : 20 * (t + 1) = 20 + 20 * t := by ring
      rw [hmul, Nat.shiftRight_add]
      have hdiv : (c * (1 + (u <<< 20))) >>> 20 = c * u := by
        simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
        have heq : c * (1 + u * 2 ^ 20) = c + (c * u) * 2 ^ 20 := by ring
        rw [heq]
        omega
      rw [hdiv]
      exact ih m (by omega)

private lemma box_mod_step (X i : ℕ) :
    X % (2 ^ (20 * (i + 1))) = X % (2 ^ (20 * i)) + (2 ^ (20 * i)) * ((X >>> (20 * i)) % (2 ^ 20)) := by
  set S := 2 ^ (20 * i)
  set T := 2 ^ 20
  have hpow : 2 ^ (20 * (i + 1)) = S * T := by
    dsimp only [S, T]; rw [← Nat.pow_add]; ring_nf
  rw [hpow, Nat.shiftRight_eq_div_pow]
  have h1 : X = S * (X / S) + X % S := (Nat.div_add_mod X S).symm
  have h2 : X / S = T * ((X / S) / T) + (X / S) % T := (Nat.div_add_mod (X / S) T).symm
  have h3 : X % S + 1 ≤ S := Nat.mod_lt X (Nat.two_pow_pos (20 * i))
  have h4 : (X / S) % T + 1 ≤ T := Nat.mod_lt (X / S) (by decide : 0 < 2 ^ 20)
  have hX : X = (X % S + S * ((X / S) % T)) + (S * T) * ((X / S) / T) := by
    calc X = S * (X / S) + X % S := h1
      _ = S * (T * ((X / S) / T) + (X / S) % T) + X % S := by rw [← h2]
      _ = (X % S + S * ((X / S) % T)) + (S * T) * ((X / S) / T) := by ring
  have hlt : X % S + S * ((X / S) % T) < S * T := by nlinarith
  conv_lhs => rw [hX]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

private lemma box_lane_add_mod {cnt X Y : ℕ}
    (h : ∀ k < cnt, ((X >>> (20 * k)) % (2 ^ 20)) + ((Y >>> (20 * k)) % (2 ^ 20)) < 2 ^ 20) :
    ∀ i ≤ cnt, X % (2 ^ (20 * i)) + Y % (2 ^ (20 * i)) < 2 ^ (20 * i) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [mul_zero, pow_zero]
    omega
  | succ i ih =>
    intro hi
    rw [box_mod_step X i, box_mod_step Y i]
    set S := 2 ^ (20 * i)
    set T := 2 ^ 20
    have hlo : (X % S + Y % S) + 1 ≤ S := ih (by omega)
    have hhi : (((X >>> (20 * i)) % T) + ((Y >>> (20 * i)) % T)) + 1 ≤ T := h i (by omega)
    have hpow : 2 ^ (20 * (i + 1)) = S * T := by
      dsimp only [S, T]; rw [← Nat.pow_add]; ring_nf
    rw [hpow]
    nlinarith

private lemma box_lane_add_lt {cnt X Y : ℕ}
    (hX : X < 2 ^ (20 * cnt)) (hY : Y < 2 ^ (20 * cnt))
    (h : ∀ k < cnt, ((X >>> (20 * k)) % (2 ^ 20)) + ((Y >>> (20 * k)) % (2 ^ 20)) < 2 ^ 20) :
    X + Y < 2 ^ (20 * cnt) := by
  have hall := box_lane_add_mod h cnt le_rfl
  rwa [Nat.mod_eq_of_lt hX, Nat.mod_eq_of_lt hY] at hall

private lemma box_lane_add_get {cnt X Y : ℕ}
    (h : ∀ k < cnt, ((X >>> (20 * k)) % (2 ^ 20)) + ((Y >>> (20 * k)) % (2 ^ 20)) < 2 ^ 20)
    {t : ℕ} (ht : t < cnt) :
    (((X + Y) >>> (20 * t)) % (2 ^ 20)) =
      ((X >>> (20 * t)) % (2 ^ 20)) + ((Y >>> (20 * t)) % (2 ^ 20)) := by
  have hlo := box_lane_add_mod h t (by omega)
  have hhi := h t ht
  set S := 2 ^ (20 * t)
  have hS : 0 < S := Nat.two_pow_pos (20 * t)
  simp only [Nat.shiftRight_eq_div_pow] at hhi ⊢
  have hdiv : (X + Y) / S = X / S + Y / S := by
    have hX := (Nat.div_add_mod X S).symm
    have hY := (Nat.div_add_mod Y S).symm
    have hsum : X + Y = (X % S + Y % S) + S * (X / S + Y / S) := by linarith
    rw [hsum, Nat.add_mul_div_left _ _ hS, Nat.div_eq_of_lt hlo, zero_add]
  change ((X + Y) / S) % (2 ^ 20) = (X / S) % (2 ^ 20) + (Y / S) % (2 ^ 20)
  rw [hdiv, Nat.add_mod, Nat.mod_eq_of_lt hhi]

private lemma box_lane_sub_mod {cnt M A : ℕ}
    (h : ∀ k < cnt, ((A >>> (20 * k)) % (2 ^ 20)) ≤ ((M >>> (20 * k)) % (2 ^ 20))) :
    ∀ i ≤ cnt, A % (2 ^ (20 * i)) ≤ M % (2 ^ (20 * i)) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [mul_zero, pow_zero]
    omega
  | succ i ih =>
    intro hi
    rw [box_mod_step A i, box_mod_step M i]
    have hlo := ih (by omega)
    have hhi := Nat.mul_le_mul_left (2 ^ (20 * i)) (h i (by omega))
    omega

private lemma box_swar_le {cnt Gc Bv A : ℕ}
    (hG : ∀ k < cnt, ((Gc >>> (20 * k)) % (2 ^ 20)) = 2 ^ 19)
    (hB : ∀ k < cnt, ((Bv >>> (20 * k)) % (2 ^ 20)) < 2 ^ 19)
    (hA : ∀ k < cnt, ((A >>> (20 * k)) % (2 ^ 20)) < 2 ^ 19)
    (hAlt : A < 2 ^ (20 * cnt))
    (hchk : (((Gc + Bv - A) &&& Gc) == Gc) = true) :
    ∀ t < cnt, ((A >>> (20 * t)) % (2 ^ 20)) ≤ ((Bv >>> (20 * t)) % (2 ^ 20)) := by
  rw [beq_iff_eq] at hchk
  have hM_lane : ∀ k < cnt, (((Gc + Bv) >>> (20 * k)) % (2 ^ 20)) = 2 ^ 19 + ((Bv >>> (20 * k)) % (2 ^ 20)) := by
    intro k hk
    rw [box_lane_add_get ?_ hk, hG k hk]
    intro j hj
    have := hG j hj
    have := hB j hj
    omega
  have hAM_lane : ∀ k < cnt, ((A >>> (20 * k)) % (2 ^ 20)) ≤ (((Gc + Bv) >>> (20 * k)) % (2 ^ 20)) := by
    intro k hk
    rw [hM_lane k hk]
    have := hA k hk
    omega
  have hAM_all := box_lane_sub_mod hAM_lane cnt le_rfl
  rw [Nat.mod_eq_of_lt hAlt] at hAM_all
  have hAleM : A ≤ Gc + Bv := hAM_all.trans (Nat.mod_le (Gc + Bv) _)
  intro t ht
  have hlo := box_lane_sub_mod hAM_lane t (by omega)
  set M := Gc + Bv
  set S := 2 ^ (20 * t)
  have hS : 0 < S := Nat.two_pow_pos (20 * t)
  have hdiv : (M - A) / S = M / S - A / S := by
    have hM := (Nat.div_add_mod M S).symm
    have hAeq := (Nat.div_add_mod A S).symm
    have hle_div : A / S ≤ M / S := Nat.div_le_div_right hAleM
    have hdiff : M - A = (M % S - A % S) + S * (M / S - A / S) := by
      have h1 : S * (M / S - A / S) = S * (M / S) - S * (A / S) := Nat.mul_sub_left_distrib S _ _
      have h2 : S * (A / S) ≤ S * (M / S) := Nat.mul_le_mul_left S hle_div
      omega
    have hlt : M % S - A % S < S := (Nat.sub_le _ _).trans_lt (Nat.mod_lt M hS)
    rw [hdiff, Nat.add_mul_div_left _ _ hS, Nat.div_eq_of_lt hlt, zero_add]
  have hmod : ((M - A) >>> (20 * t)) % (2 ^ 20) = 2 ^ 19 + ((Bv >>> (20 * t)) % (2 ^ 20)) - ((A >>> (20 * t)) % (2 ^ 20)) := by
    have hm_t : (M / S) % (2 ^ 20) = 2 ^ 19 + ((Bv / S) % (2 ^ 20)) := by
      simpa only [Nat.shiftRight_eq_div_pow] using hM_lane t ht
    have hrem_le : (A / S) % (2 ^ 20) ≤ (M / S) % (2 ^ 20) := by
      simpa only [Nat.shiftRight_eq_div_pow] using hAM_lane t ht
    simp only [Nat.shiftRight_eq_div_pow]
    change ((M - A) / S) % (2 ^ 20) = 2 ^ 19 + ((Bv / S) % (2 ^ 20)) - ((A / S) % (2 ^ 20))
    rw [hdiv]
    have hle_q : A / S ≤ M / S := Nat.div_le_div_right hAleM
    have hM' := (Nat.div_add_mod (M / S) (2 ^ 20)).symm
    have hA' := (Nat.div_add_mod (A / S) (2 ^ 20)).symm
    have hle_qq : (A / S) / (2 ^ 20) ≤ (M / S) / (2 ^ 20) := Nat.div_le_div_right hle_q
    have hdiff2 : M / S - A / S = ((M / S) % (2 ^ 20) - (A / S) % (2 ^ 20)) + (2 ^ 20) * ((M / S) / (2 ^ 20) - (A / S) / (2 ^ 20)) := by
      have h1 : (2 ^ 20) * ((M / S) / (2 ^ 20) - (A / S) / (2 ^ 20)) = (2 ^ 20) * ((M / S) / (2 ^ 20)) - (2 ^ 20) * ((A / S) / (2 ^ 20)) :=
        Nat.mul_sub_left_distrib (2 ^ 20) _ _
      have h2 : (2 ^ 20) * ((A / S) / (2 ^ 20)) ≤ (2 ^ 20) * ((M / S) / (2 ^ 20)) :=
        Nat.mul_le_mul_left (2 ^ 20) hle_qq
      omega
    have hlt2 : (M / S) % (2 ^ 20) - (A / S) % (2 ^ 20) < 2 ^ 20 :=
      (Nat.sub_le _ _).trans_lt (Nat.mod_lt _ (by decide))
    rw [hdiff2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2, hm_t]
  have hGbit : Gc.testBit (20 * t + 19) = true := by
    have hg_t := hG t ht
    rw [← Nat.testBit_shiftRight]
    have hmod_tb : ((Gc >>> (20 * t)) % (2 ^ 20)).testBit 19 = (Gc >>> (20 * t)).testBit 19 := by
      rw [← Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_land, Nat.testBit_two_pow_sub_one]
      simp
    rw [← hmod_tb, hg_t]
    decide
  have hMAbit : (M - A).testBit (20 * t + 19) = true := by
    have h := congrArg (fun x => x.testBit (20 * t + 19)) hchk
    rw [Nat.testBit_land, hGbit, Bool.and_true] at h
    exact h
  have hMA_ge : 2 ^ 19 ≤ ((M - A) >>> (20 * t)) % (2 ^ 20) := by
    by_contra hlt19
    push Not at hlt19
    have htb : (((M - A) >>> (20 * t)) % (2 ^ 20)).testBit 19 = false :=
      Nat.testBit_eq_false_of_lt hlt19
    rw [← Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_land, Nat.testBit_two_pow_sub_one] at htb
    simp only [show (19 < 20) = True by decide, decide_true, Bool.and_true] at htb
    rw [Nat.testBit_shiftRight, hMAbit] at htb
    cases htb
  have hb_t := hB t ht
  have ha_t := hA t ht
  omega

-- 4. Kernel-verified packed prime certificate

private theorem box_cert :
    ∃ P O : ℕ,
      O * 0xFFFFF = (1 <<< (20 * 1008)) - 1 ∧
      (P &&& 0xFFFFF) = 2 ∧
      ((P >>> (20 * 1007)) &&& 0xFFFFF) = 8009 ∧
      (P &&& ((O <<< 19) ||| (O <<< 18))) = 0 ∧
      (((((O >>> 20) <<< 19) + (P >>> 20) -
          ((P &&& ((1 <<< (20 * 1007)) - 1)) + (O >>> 20))) &&&
        ((O >>> 20) <<< 19)) == ((O >>> 20) <<< 19)) = true ∧
      (Nat.rec (motive := fun _ => ℕ → ℕ)
          (fun X => 1 <<< (X &&& 0xFFFFF))
          (fun k rec X => rec X ||| rec (X >>> (20 <<< k)))
          9 P |||
        Nat.rec (motive := fun _ => ℕ → ℕ)
          (fun X => 1 <<< (X &&& 0xFFFFF))
          (fun k rec X => rec X ||| rec (X >>> (20 <<< k)))
          9 (P >>> (20 * 496))) =
      ((((1 <<< (8009 - 1)) - 1) <<< 2) ^^^
        ((((1 <<< (8009 - 1)) - 1) <<< 2) &&&
          List.foldl
            (fun acc q =>
              acc ||| (((Nat.rec (motive := fun _ => ℕ) 1 (fun k m => m ||| (m <<< (q <<< k))) 13) >>> (2 * q)) <<< (2 * q)))
            0 ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89] : List ℕ))) ∧
      ((List.range 503).all (fun m =>
        ((((((O >>> (40 * (m + 1))) <<< 19) + (P >>> (40 * (m + 1)))) -
           ((((P >>> (20 * (m + 1))) &&& 0xFFFFF) - 1) * (O >>> (40 * (m + 1))) +
            ((P >>> (20 * (m + 1))) &&& ((1 <<< (20 * (1008 - 2 * (m + 1)))) - 1)))) &&&
          ((O >>> (40 * (m + 1))) <<< 19)) == ((O >>> (40 * (m + 1))) <<< 19)))) = true :=
  ⟨0x01f4901f3901f1b01f0f01f0d01f0101efd01ef701eef01ee301edd01ecb01ec701ec501ec101ebb01ead01ea101e9501e8f01e8901e7101e6d01e4f01e4d01e4901e3d01e2f01e2b01e2501e1701e1301e0b01e0701e0101df901df501de101ddb01dd701dc501db701db301da701da501d9f01d9901d9501d8901d8701d7d01d7b01d7501d7101d6901d6301d5d01d5301d4b01d4101d3f01d3901d3501d2301d2101d1b01d0901cf901cf301ce101cc901cb701cb501ca501ca301c9901c8d01c8b01c8101c7301c5501c4f01c4b01c4501c3d01c3301c2d01c2b01c2701c1901c1301c0901bf701bef01bd901bd701bd101bc501bbf01ba701b9d01b9101b8301b7f01b7301b6b01b6501b5901b5501b4f01b4701b4101b3b01b3701b3101b2f01b2501b2301b0501aff01afb01af301ae301ad701ad501acf01ac901ab901ab101aad01aab01aa701a9301a8901a8701a7d01a7b01a6b01a6901a5101a4d01a3f01a3501a2f01a2d01a2301a2101a1701a1101a0501a03019fd019ed019db019cf019c7019b5019b1019ab019a9019a301999019970199301981019790195b01951019490194501933019310191b01915018fd018f5018eb018e5018df018d9018d7018d1018c7018c1018b9018b3018ad018a70189d0189b0188f018850187f0187d018770187101867018550184d01849018430183b01837018350181d0181301807017ff017f5017f3017e9017e1017d5017cb017c9017bf017b9017b3017a50179f0179b017950178d0177b01777017630175d017410173301727017230170f01709016f9016f7016ed016eb016e5016e1016db016d9016d3016cf016c3016bd016b5016af016a90169f0169701693016750166f0166d01669016550164f016450163d0163901633016250161b0161901615016130160f0160901607015f7015d7015cd015c5015c1015bb015b50159b01597015910158f015830157f0157d0156b01567015650155f0154901543015410153d015370152b01529015250151f01517015110150b01505014e7014e3014d5014cb014bd014b7014b1014a10149f014990148d01475014710146f0146b014590144d014450143b014330142f014210141b013ff013f9013f3013ed013eb013df013d9013d5013c3013bb013af0139f0139d01393013910138b01387013810137b0136d01369013670135d013570134f013490134501343013370132d01327013190130d01307012fd012df012d1012cd012c1012bf012b9012b5012b3012af012970128f0127d0127901273012710125f01253012470124101237012310122b01229012230121f0121d0120d011fb011f5011ef011e7011d7011d1011c5011c3011ab011a7011a5011a10119b0118d01183011810116f01169011630115f011590114701145011390112d01127011150110b01105010fd010f3010f1010e7010c9010c1010bb010b1010af010a5010a30109d010930109101087010850107b010790107301069010510103f0103d010390102b01025010210101f0100f0100300ffd00ffb00fef00fe900fd900fd300fd100fbb00fb500fb300fad00fa700fa300fa100f9500f7f00f6b00f6700f5b00f5900f5300f4f00f4d00f4700f4300f3100f2900f2500f1700f0d00f0b00f0700ef900eef00eed00edb00ed500ed100ec300eb900eb700eb100e9b00e9500e8f00e8700e7d00e7500e7100e6b00e5d00e5900e5700e4b00e3b00e3500e2f00e2700e2100e1d00e1700e0900dff00dfd00df300de700de500ddb00dd500dd300dcd00dc900dc700dbd00db700dab00da300d8d00d8b00d8700d8500d8100d7900d6900d5500d4f00d3f00d3d00d2d00d2b00d2100d1f00d1300d0f00d0300d0100cfb00cf700cf100ceb00ce500ce300cc700cbb00cb900cb500cb300c9d00c9500c9100c8900c8300c7700c7300c6d00c6100c5f00c5b00c4100c3100c2f00c2500c1100c0b00c0700bfb00bf500be900be100bdd00bcf00bcb00bc300bb900bb700b9b00b9900b9300b8d00b8900b7b00b6f00b6500b5d00b5700b5100b4700b3f00b2d00b2900b2300b1b00b1500b1100b0300af300af100aed00ae700ae500ad900acf00ac100abd00ab500aab00aa900a9f00a9900a9700a9300a8b00a8500a8100a7f00a7b00a7500a6f00a6700a6300a6100a5700a4900a3d00a3900a3100a2100a1f00a13009fd009f7009f5009ef009eb009e3009d9009c7009ad009a9009a30099b0098f009890098500977009710096b0095f00959009550094f0094d0094900943009350092f0092b00925009230091d0090700905008f9008f5008ef008e9008e1008dd008db008cb008c3008bf008bd008ad008a50089f0089b0088300871008690085f0085d008590085300851008410083f0083300829008270082300821008150080f00805007f7007ed007eb007e1007db007d3007cf007cd007c9007c3007bb007b50079f0079d0078d0078b00779007730076d007610075700755007510074f0074b0074500737007270071f0071300709006fd006fb006f7006f1006df006d9006d3006cd006c5006bb006b9006ad006a3006a10069d00685006830067f00679006650065b00655006530064d0064900647006410063d0062f0062b006230061f00617006110060d00607005fb005f3005e7005db005d5005d1005cf005cb005c9005bf005b3005ad005ab005a70059f0059900595005930058f0058100577005650055d00557005510052f00529005270051b0051700515005110050b0050900503004ff004fd004eb004e1004d5004cf004cd004c7004c1004bd004b1004a9004a30049d004930048b004810047f00469004630045d004550044f0044900445004430043f0042d00427004250041b004190040f0040900407003fd003fb003f5003f1003e5003df003d7003d1003cb003c7003b9003b3003ad003a9003a1003970038f0038b0037700373003710036d0035f0035b0035900355003470033d0033b00337003350032b003290031d003130030500301002f9002f5002ef002e7002e3002dd002d7002cf002c5002bd002b3002ab002a5002a100295002930028d002870028300281002770026b00269002650025f0025900257002510024b002410023b00239002330022d002230021d0020b00209001fd001f7001f3001eb001e7001df001d3001cf001cd001c9001c1001bb001b7001b1001af001a5001a300199001910018d001850017f0017b001750016f00167001610015d0015b001510014b0013d001390013700133001250011b00119001150010f0010d0010700101000fb000f1000ef000e9000e5000e3000df000d3000c7000c5000c1000bf000b5000b3000ad000a7000a30009d00097000950008b00089000830007f000710006d0006b00067000650006100059000530004f0004900047000430003d0003b000350002f0002b00029000250001f0001d0001700013000110000d0000b00007000050000300002, 0x000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001000010000100001, by decide +kernel⟩

-- 5. Unconditional finite-box prime-counting subadditivity theorem

theorem box_bound : ∀ x y : ℕ, 2 ≤ x → 2 ≤ y → x + y ≤ 8000 →
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  obtain ⟨P, O, hOmul, hP0, hPK, hP18, hMono_chk, hTree, hSwar⟩ := box_cert
  have hO : O = Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) 1008 :=
    box_ones_eq_of_mul 1008 O hOmul
  clear hOmul
  set p : ℕ → ℕ := fun k => (P >>> (20 * k)) &&& 0xFFFFF
  have hp_mod : ∀ k, p k = (P >>> (20 * k)) % (2 ^ 20) := by
    intro k
    change (P >>> (20 * k)) &&& (2 ^ 20 - 1) = (P >>> (20 * k)) % (2 ^ 20)
    exact Nat.and_two_pow_sub_one_eq_mod _ 20
  -- Every lane k < 1008 of P is < 2^18
  have hp_lt18 : ∀ k < 1008, p k < 2 ^ 18 := by
    intro k hk
    rw [hp_mod]
    have hO19 : (O <<< 19).testBit (20 * k + 19) = true := by
      have hc : (2 ^ 19 : ℕ) < 2 ^ 20 := by decide
      have hlane := box_mul_ones_lane hc k 1008 hk
      rw [← hO] at hlane
      have hmul : O <<< 19 = 2 ^ 19 * O := by rw [Nat.shiftLeft_eq, mul_comm]
      rw [hmul, ← Nat.testBit_shiftRight]
      have htb : (((2 ^ 19 * O) >>> (20 * k)) % (2 ^ 20)).testBit 19 = ((2 ^ 19 * O) >>> (20 * k)).testBit 19 := by
        rw [← Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_land, Nat.testBit_two_pow_sub_one]
        simp
      rw [← htb, hlane]
      decide
    have hO18 : (O <<< 18).testBit (20 * k + 18) = true := by
      have hc : (2 ^ 18 : ℕ) < 2 ^ 20 := by decide
      have hlane := box_mul_ones_lane hc k 1008 hk
      rw [← hO] at hlane
      have hmul : O <<< 18 = 2 ^ 18 * O := by rw [Nat.shiftLeft_eq, mul_comm]
      rw [hmul, ← Nat.testBit_shiftRight]
      have htb : (((2 ^ 18 * O) >>> (20 * k)) % (2 ^ 20)).testBit 18 = ((2 ^ 18 * O) >>> (20 * k)).testBit 18 := by
        rw [← Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_land, Nat.testBit_two_pow_sub_one]
        simp
      rw [← htb, hlane]
      decide
    have hz19 := congrArg (fun z => z.testBit (20 * k + 19)) hP18
    rw [Nat.testBit_land, Nat.testBit_lor, hO19, Bool.true_or, Bool.and_true, Nat.zero_testBit,
      ← Nat.testBit_shiftRight] at hz19
    have hz18 := congrArg (fun z => z.testBit (20 * k + 18)) hP18
    rw [Nat.testBit_land, Nat.testBit_lor, hO18, Bool.or_true, Bool.and_true, Nat.zero_testBit,
      ← Nat.testBit_shiftRight] at hz18
    exact box_lt18_of_bits hz18 hz19
  -- Strict monotonicity: p k + 1 ≤ p (k + 1) for k < 1007
  have hp_step : ∀ k < 1007, p k + 1 ≤ p (k + 1) := by
    have hO_sub : O >>> 20 = Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) 1007 := by
      have hsh := box_ones_shift 1 1008 (by decide)
      rw [← hO] at hsh
      exact hsh
    set O_K := O >>> 20
    have hG_lane : ∀ k < 1007, (((O_K <<< 19) >>> (20 * k)) % (2 ^ 20)) = 2 ^ 19 := by
      intro k hk
      have hmul : O_K <<< 19 = 2 ^ 19 * O_K := by rw [Nat.shiftLeft_eq, mul_comm]
      rw [hmul, hO_sub]
      exact box_mul_ones_lane (by decide) k 1007 hk
    have hB_lane : ∀ k < 1007, (((P >>> 20) >>> (20 * k)) % (2 ^ 20)) < 2 ^ 19 := by
      intro k hk
      rw [← Nat.shiftRight_add]
      have heq : 20 + 20 * k = 20 * (k + 1) := by ring
      rw [heq, ← hp_mod]
      have := hp_lt18 (k + 1) (by omega)
      omega
    set P_lo := P &&& ((1 <<< (20 * 1007)) - 1)
    have hPlo_lane : ∀ k < 1007, ((P_lo >>> (20 * k)) % (2 ^ 20)) = p k := by
      intro k hk
      have := box_sub_lane P 0 1007 k hk
      rw [Nat.mul_zero, Nat.shiftRight_zero, zero_add] at this
      exact this
    have hOK_lane : ∀ k < 1007, ((O_K >>> (20 * k)) % (2 ^ 20)) = 1 := by
      intro k hk
      have h1 : O_K = 1 * O_K := (one_mul O_K).symm
      rw [h1, hO_sub]
      exact box_mul_ones_lane (by decide) k 1007 hk
    have hsum_lt : ∀ k < 1007, ((P_lo >>> (20 * k)) % (2 ^ 20)) + ((O_K >>> (20 * k)) % (2 ^ 20)) < 2 ^ 20 := by
      intro k hk
      rw [hPlo_lane k hk, hOK_lane k hk]
      have := hp_lt18 k (by omega)
      omega
    have hA_lane : ∀ k < 1007, (((P_lo + O_K) >>> (20 * k)) % (2 ^ 20)) < 2 ^ 19 := by
      intro k hk
      rw [box_lane_add_get hsum_lt hk, hPlo_lane k hk, hOK_lane k hk]
      have := hp_lt18 k (by omega)
      omega
    have hle := box_swar_le hG_lane hB_lane hA_lane
      (box_lane_add_lt (box_and_mask_lt P (20 * 1007)) (hO_sub ▸ box_ones_lt 1007) hsum_lt) hMono_chk
    intro k hk
    have hk_le := hle k hk
    rw [box_lane_add_get hsum_lt hk, hPlo_lane k hk, hOK_lane k hk] at hk_le
    rw [← Nat.shiftRight_add] at hk_le
    have heq : 20 + 20 * k = 20 * (k + 1) := by ring
    rw [heq, ← hp_mod] at hk_le
    exact hk_le
  -- Connect treeMask = primeMask to primality and completeness of p 0 .. p 1007
  have hp_iff : ∀ j : ℕ, (∃ k < 1008, p k = j) ↔ (j ≤ 8009 ∧ Nat.Prime j) := by
    intro j
    rw [← box_primeMask_iff j, ← hTree, Nat.testBit_lor, Bool.or_eq_true,
      box_tree_testBit, box_tree_testBit]
    have hwin : (1 <<< 9) = 512 := by decide
    rw [hwin]
    constructor
    · rintro ⟨k, hk, h⟩
      by_cases hlt : k < 512
      · exact Or.inl ⟨k, hlt, h⟩
      · refine Or.inr ⟨k - 496, by omega, ?_⟩
        rw [← Nat.shiftRight_add]
        have heq : 20 * 496 + 20 * (k - 496) = 20 * k := by omega
        rw [heq]
        exact h
    · rintro (⟨k, hk, h⟩ | ⟨k, hk, h⟩)
      · exact ⟨k, by omega, h⟩
      · refine ⟨496 + k, by omega, ?_⟩
        rw [← Nat.shiftRight_add] at h
        have heq : 20 * 496 + 20 * k = 20 * (496 + k) := by ring
        rw [heq] at h
        exact h
  have hp_prime : ∀ k < 1008, Nat.Prime (p k) :=
    fun k hk => ((hp_iff (p k)).mp ⟨k, hk, rfl⟩).2
  -- Extract SWAR inequality: p a + p b - 1 ≤ p (a + b) for 1 ≤ a ≤ b and a + b ≤ 1007
  rw [List.all_eq_true] at hSwar
  have hp_add_le : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → a + b ≤ 1007 → p a + p b - 1 ≤ p (a + b) := by
    intro a b ha1 hab habK
    clear hP18 hMono_chk hTree
    have hm_mem : a - 1 ∈ List.range 503 := List.mem_range.mpr (by omega)
    have hrow := hSwar (a - 1) hm_mem
    have ha_eq : a - 1 + 1 = a := by omega
    rw [ha_eq] at hrow
    set cnt := 1008 - 2 * a
    have h2a : 2 * a ≤ 1008 := by omega
    have hO_cnt : O >>> (40 * a) = Nat.rec (motive := fun _ => ℕ) 0 (fun _ u => 1 + (u <<< 20)) cnt := by
      have hmul : 40 * a = 20 * (2 * a) := by ring
      rw [hmul, hO]
      exact box_ones_shift (2 * a) 1008 h2a
    set O_c := O >>> (40 * a)
    clear hO hSwar
    have hG_lane : ∀ k < cnt, (((O_c <<< 19) >>> (20 * k)) % (2 ^ 20)) = 2 ^ 19 := by
      intro k hk
      have hmul : O_c <<< 19 = 2 ^ 19 * O_c := by rw [Nat.shiftLeft_eq, mul_comm]
      rw [hmul, hO_cnt]
      exact box_mul_ones_lane (by decide) k cnt hk
    have hB_lane : ∀ k < cnt, (((P >>> (40 * a)) >>> (20 * k)) % (2 ^ 20)) < 2 ^ 19 := by
      intro k hk
      rw [← Nat.shiftRight_add]
      have heq : 40 * a + 20 * k = 20 * (2 * a + k) := by ring
      rw [heq, ← hp_mod]
      have := hp_lt18 (2 * a + k) (by omega)
      omega
    set P_sub := (P >>> (20 * a)) &&& ((1 <<< (20 * cnt)) - 1)
    have hPsub_lane : ∀ k < cnt, ((P_sub >>> (20 * k)) % (2 ^ 20)) = p (a + k) :=
      fun k hk => box_sub_lane P a cnt k hk
    have hpa_lt : p a - 1 < 2 ^ 20 := by
      have := hp_lt18 a (by omega)
      omega
    have hmul_lane : ∀ k < cnt, ((((p a - 1) * O_c) >>> (20 * k)) % (2 ^ 20)) = p a - 1 := by
      intro k hk
      rw [hO_cnt]
      exact box_mul_ones_lane hpa_lt k cnt hk
    have hsum_lt : ∀ k < cnt, ((((p a - 1) * O_c) >>> (20 * k)) % (2 ^ 20)) + ((P_sub >>> (20 * k)) % (2 ^ 20)) < 2 ^ 20 := by
      intro k hk
      rw [hmul_lane k hk, hPsub_lane k hk]
      have := hp_lt18 a (by omega)
      have := hp_lt18 (a + k) (by omega)
      omega
    have hA_lane : ∀ k < cnt, (((((p a - 1) * O_c) + P_sub) >>> (20 * k)) % (2 ^ 20)) < 2 ^ 19 := by
      intro k hk
      rw [box_lane_add_get hsum_lt hk, hmul_lane k hk, hPsub_lane k hk]
      have := hp_lt18 a (by omega)
      have := hp_lt18 (a + k) (by omega)
      omega
    have hle := box_swar_le hG_lane hB_lane hA_lane
      (box_lane_add_lt (hO_cnt ▸ box_mul_ones_lt hpa_lt) (box_and_mask_lt (P >>> (20 * a)) (20 * cnt)) hsum_lt) hrow
    have ht : b - a < cnt := by omega
    have hres := hle (b - a) ht
    rw [box_lane_add_get hsum_lt ht, hmul_lane (b - a) ht, hPsub_lane (b - a) ht] at hres
    rw [← Nat.shiftRight_add] at hres
    have heq1 : a + (b - a) = b := by omega
    have heq2 : 40 * a + 20 * (b - a) = 20 * (a + b) := by omega
    rw [heq1, heq2, ← hp_mod] at hres
    have hpa2 : 2 ≤ p a := (hp_prime a (by omega)).two_le
    clear hO_cnt hrow hle
    omega
  -- Clear all bit-level hypotheses; reason purely from p
  have hp0_eq : p 0 = 2 := by simpa [p] using hP0
  have hpK_eq : p 1007 = 8009 := hPK
  clear hO hP0 hPK hP18 hMono_chk hTree hSwar hp_mod hp_lt18
  have hp_strictMono : ∀ {a b : ℕ}, a < b → b < 1008 → p a < p b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have hstep := hp_step b (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hab with hlt | rfl
      · have := ih hlt (by omega)
        omega
      · omega
  have hp_mono : ∀ {a b : ℕ}, a ≤ b → b < 1008 → p a ≤ p b := by
    intro a b hab hb
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (hp_strictMono hlt hb).le
  have hpi_le : ∀ {n m : ℕ}, n ≤ 8009 → m < 1008 → n < p m → Nat.primeCounting n ≤ m := by
    intro n m hn hm hlt
    rw [← Nat.primesLE_card_eq_primeCounting]
    have hsub : Nat.primesLE n ⊆ (Finset.range m).image p := by
      intro q hq
      rw [Nat.mem_primesLE] at hq
      obtain ⟨hqn, hqp⟩ := hq
      obtain ⟨k, hkM, rfl⟩ := (hp_iff q).mpr ⟨hqn.trans hn, hqp⟩
      rw [Finset.mem_image]
      refine ⟨k, Finset.mem_range.mpr ?_, rfl⟩
      by_contra hkm
      have := hp_mono (by omega : m ≤ k) hkM
      omega
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  have hle_pi : ∀ {n m : ℕ}, 1 ≤ m → m ≤ 1008 → p (m - 1) ≤ n → m ≤ Nat.primeCounting n := by
    intro n m hm1 hmM hple
    rw [← Nat.primesLE_card_eq_primeCounting]
    have hsub : (Finset.range m).image p ⊆ Nat.primesLE n := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨k, hk, rfl⟩ := hq
      rw [Finset.mem_range] at hk
      rw [Nat.mem_primesLE]
      exact ⟨(hp_mono (by omega : k ≤ m - 1) (by omega)).trans hple, hp_prime k (by omega)⟩
    have hinj : Set.InjOn p (Finset.range m) := by
      intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      rcases lt_trichotomy a b with hlt | rfl | hgt
      · exact absurd hab (hp_strictMono hlt (by omega)).ne
      · rfl
      · exact absurd hab (hp_strictMono hgt (by omega)).ne'
    have hcard : ((Finset.range m).image p).card = m := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hbracket : ∀ {z : ℕ}, 2 ≤ z → z < p 1007 → ∃ m, 1 ≤ m ∧ m ≤ 1007 ∧ p (m - 1) ≤ z ∧ z < p m := by
    have haux : ∀ k ≤ 1007, ∀ z, p 0 ≤ z → z < p k → ∃ m, 1 ≤ m ∧ m ≤ k ∧ p (m - 1) ≤ z ∧ z < p m := by
      intro k
      induction k with
      | zero =>
        intro _ z h1 h2
        omega
      | succ k ih =>
        intro hk z hz0 hzk1
        by_cases hlt : z < p k
        · obtain ⟨m, hm1, hmk, hlo, hhi⟩ := ih (by omega) z hz0 hlt
          exact ⟨m, hm1, by omega, hlo, hhi⟩
        · exact ⟨k + 1, by omega, le_rfl, by simpa using Nat.le_of_not_lt hlt, hzk1⟩
    intro z hz2 hzk
    exact haux 1007 le_rfl z (by omega) hzk
  intro x y hx hy hxy
  have hxK : x < p 1007 := by omega
  have hyK : y < p 1007 := by omega
  obtain ⟨m, hm1, hmK, hmx_lo, hmx_hi⟩ := hbracket hx hxK
  obtain ⟨n, hn1, hnK, hny_lo, hny_hi⟩ := hbracket hy hyK
  have hpi_x : m ≤ Nat.primeCounting x := hle_pi hm1 (by omega) hmx_lo
  have hpi_y : n ≤ Nat.primeCounting y := hle_pi hn1 (by omega) hny_lo
  by_cases hsumK : 1007 ≤ m + n
  · have hpi_xy : Nat.primeCounting (x + y) ≤ 1007 :=
      hpi_le (by omega) (by omega) (by omega)
    omega
  · have hmn_le : m + n ≤ 1007 := by omega
    have hpm_pn : p m + p n - 1 ≤ p (m + n) := by
      by_cases hmn : m ≤ n
      · exact hp_add_le hm1 hmn hmn_le
      · have hnm := hp_add_le hn1 (by omega : n ≤ m) (by omega : n + m ≤ 1007)
        rw [Nat.add_comm n m] at hnm
        omega
    have hxy_lt : x + y < p (m + n) := by omega
    have hpi_xy : Nat.primeCounting (x + y) ≤ m + n :=
      hpi_le (by omega) (by omega) hxy_lt
    omega

/-- **Balanced regime (Udrescu 1975)**: Second Hardy–Littlewood inequality for critical pairs
with `216 < x ≤ y ≤ x ^ 2` and `8000 < x + y`. -/
def H1 : Prop :=
  ∀ x y : ℕ, 216 < x → x ≤ y → y ≤ x ^ 2 → 8000 < x + y →
    Nat.Prime (x + y) → (Nat.Prime (x + 1) ∨ Nat.Prime y ∨ y ≤ x + 1) →
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y

/-- **Skew regime (Hensley–Richards 1974)**: Second Hardy–Littlewood inequality for super-quadratic
critical pairs with `216 < x`, `x ≤ y`, `x ^ 2 < y`, and `8000 < x + y`. -/
def H2 : Prop :=
  ∀ x y : ℕ, 216 < x → x ≤ y → x ^ 2 < y → 8000 < x + y →
    Nat.Prime (x + y) → (Nat.Prime (x + 1) ∨ Nat.Prime y ∨ y ≤ x + 1) →
    Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000720.main := by
  intro h1 h2
  refine wlog_prime_sum_reduction 8000 box_bound (fun x y hx hxy hB hp hb => ?_)
  by_cases hsq : y ≤ x ^ 2
  · exact h1 x y hx hxy hsq hB hp hb
  · exact h2 x y hx hxy (lt_of_not_ge hsq) hB hp hb

end OMA.R_oeis_a000720_R1
