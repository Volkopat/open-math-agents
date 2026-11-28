import OMAReductions.R_OeisA232194_conjecture_4_R1

namespace OMA.Proof_OeisA232194_conjecture_4_R1_H1

private def noDivUpTo (q : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | d + 1 => (q % (d + 1) != 0) && noDivUpTo q d

private lemma not_dvd_of_noDivUpTo {q m d : ℕ} (h : noDivUpTo q m = true)
    (hd2 : 2 ≤ d) (hdm : d ≤ m) : ¬ d ∣ q := by
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => omega
    | succ m' =>
      unfold noDivUpTo at h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      by_cases hEq : d = m' + 2
      · subst hEq
        intro hdvd
        exact h.1 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih h.2 (by omega)

private lemma prime_of_trial {q m : ℕ} (hq2 : 2 ≤ q) (hm : q < (m + 1) * (m + 1))
    (hnd : noDivUpTo q m = true) : q.Prime := by
  rw [Nat.prime_def_lt']
  refine ⟨hq2, fun d hd2 hdlt hdvd => ?_⟩
  by_cases hle : d ≤ m
  · exact not_dvd_of_noDivUpTo hnd hd2 hle hdvd
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
    have hqle : q / d ≤ m := by nlinarith
    exact not_dvd_of_noDivUpTo hnd hq2' hqle hqdiv

private def powModAux (a q : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel + 1, e =>
    if e == 0 then 1
    else
      let half := powModAux a q fuel (e / 2)
      let sq := (half * half) % q
      if e % 2 == 1 then (sq * a) % q else sq

private def powMod (a e q : ℕ) : ℕ := powModAux (a % q) q 24 e

private lemma powModAux_eq (a q fuel e : ℕ) (he : e < 2 ^ fuel) (hq : 2 ≤ q) :
    powModAux a q fuel e = a ^ e % q := by
  induction fuel generalizing e with
  | zero =>
    have he0 : e = 0 := by simp at he; omega
    subst he0
    simp [powModAux, Nat.mod_eq_of_lt (by omega : 1 < q)]
  | succ f ih =>
    unfold powModAux
    by_cases he0 : e = 0
    · subst he0; simp [Nat.mod_eq_of_lt (by omega : 1 < q)]
    · simp only [beq_iff_eq, he0, ↓reduceIte]
      have hlt : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
      have hih := ih (e / 2) hlt
      rw [hih]
      have hsq : (a ^ (e / 2) % q * (a ^ (e / 2) % q)) % q = a ^ (2 * (e / 2)) % q := by
        rw [← Nat.mul_mod, ← pow_add, two_mul]
      rw [hsq]
      by_cases hodd : e % 2 = 1
      · simp only [hodd, ↓reduceIte]
        rw [Nat.mod_mul_mod, ← pow_succ, show 2 * (e / 2) + 1 = e by omega]
      · simp only [hodd, ↓reduceIte]
        rw [show 2 * (e / 2) = e by omega]

private lemma powMod_eq (a e q : ℕ) (he : e < 2 ^ 24) (hq : 2 ≤ q) :
    powMod a e q = a ^ e % q := by
  unfold powMod
  rw [powModAux_eq (a % q) q 24 e he hq, ← Nat.pow_mod]

private def stripPrime (p : ℕ) : ℕ → ℕ → ℕ
  | 0, n => n
  | fuel + 1, n => if 1 < p && n % p == 0 then stripPrime p fuel (n / p) else n

private lemma stripPrime_dvd_of_ne {p fuel n r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hrn : r ∣ n) (hrne : r ≠ p) : r ∣ stripPrime p fuel n := by
  induction fuel generalizing n with
  | zero => exact hrn
  | succ f ih =>
    unfold stripPrime
    by_cases hc : 1 < p ∧ n % p = 0
    · have hcond : (decide (1 < p) && (n % p == 0)) = true := by
        simp [hc.1, hc.2]
      rw [if_pos hcond]
      apply ih
      have hpdvd : p ∣ n := Nat.dvd_of_mod_eq_zero hc.2
      have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpdvd
      rw [← hmul] at hrn
      rcases hr.dvd_mul.mp hrn with hrp | hrd
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).mp hrp) hrne
      · exact hrd
    · have hcond : ¬ (decide (1 < p) && (n % p == 0)) = true := by
        simp [hc]
      rw [if_neg hcond]
      exact hrn

private def stripList : List ℕ → ℕ → ℕ
  | [], n => n
  | p :: ps, n => stripList ps (stripPrime p 24 n)

private lemma mem_of_stripList_eq_one {ps : List ℕ} {n r : ℕ}
    (hps : ∀ p ∈ ps, p.Prime) (hr : r.Prime) (hrn : r ∣ n)
    (h1 : stripList ps n = 1) : r ∈ ps := by
  by_contra hnot
  have hdvd : ∀ (ls : List ℕ) (m : ℕ), (∀ p ∈ ls, p.Prime) → r ∉ ls → r ∣ m → r ∣ stripList ls m := by
    intro ls
    induction ls with
    | nil => intro m _ _ hm; exact hm
    | cons p rest ih =>
      intro m hpr hnr hm
      apply ih (stripPrime p 24 m) (fun x hx => hpr x (List.mem_cons_of_mem p hx))
        (fun hx => hnr (List.mem_cons_of_mem p hx))
      exact stripPrime_dvd_of_ne (hpr p (by simp)) hr hm (fun heq => hnr (by simp [heq]))
  have hdiv1 := hdvd ps n hps hnot hrn
  rw [h1] at hdiv1
  exact hr.not_dvd_one hdiv1

private lemma prime_of_lucas {q a : ℕ} {rs : List ℕ} (hq : 2 ≤ q)
    (hq_lt : q - 1 < 2 ^ 24)
    (hrs : ∀ r ∈ rs, r.Prime)
    (hstrip : stripList rs (q - 1) = 1)
    (hpow1 : powMod a (q - 1) q = 1)
    (hpowr : ∀ r ∈ rs, powMod a ((q - 1) / r) q ≠ 1) : q.Prime := by
  have : NeZero q := ⟨by omega⟩
  have : Fact (1 < q) := ⟨by omega⟩
  have ha_pow : a ^ (q - 1) % q = 1 := by
    rw [← powMod_eq a (q - 1) q hq_lt hq]; exact hpow1
  have hcop : Nat.Coprime a q := by
    have h1 : Nat.gcd (a ^ (q - 1)) q = 1 := by
      rw [Nat.gcd_comm, Nat.gcd_rec, ha_pow]; simp
    exact (Nat.coprime_pow_left_iff (by omega : 0 < q - 1) a q).mp h1
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a hcop
  have hu_val : ∀ k : ℕ, ((u ^ k : (ZMod q)ˣ) : ZMod q) = (a ^ k : ZMod q) := by
    intro k; simp [u, ZMod.coe_unitOfCoprime]
  have hu_pow : u ^ (q - 1) = 1 := by
    apply Units.ext
    rw [hu_val, Units.val_one]
    rw [← Nat.cast_pow, ← ZMod.natCast_mod, ha_pow, Nat.cast_one]
  have hord_dvd : orderOf u ∣ q - 1 := orderOf_dvd_of_pow_eq_one hu_pow
  have hord_eq : orderOf u = q - 1 := by
    by_contra hne
    obtain ⟨m, hm⟩ := hord_dvd
    have hm1 : m ≠ 1 := by intro h; rw [h, mul_one] at hm; exact hne hm.symm
    have hm0 : m ≠ 0 := by intro h; rw [h, mul_zero] at hm; omega
    obtain ⟨r, hrp, hrm⟩ := Nat.exists_prime_and_dvd hm1
    have hrq : r ∣ q - 1 := hrm.trans ⟨orderOf u, by linarith⟩
    have hrmem : r ∈ rs := mem_of_stripList_eq_one hrs hrp hrq hstrip
    have hord_dvd_div : orderOf u ∣ (q - 1) / r := by
      obtain ⟨c, hc⟩ := hrm
      refine ⟨c, ?_⟩
      have : q - 1 = r * (orderOf u * c) := by rw [hm, hc]; ring
      rw [this, Nat.mul_div_cancel_left _ hrp.pos]
    have hu_div : u ^ ((q - 1) / r) = 1 := orderOf_dvd_iff_pow_eq_one.mp hord_dvd_div
    have hmod1 : a ^ ((q - 1) / r) % q = 1 := by
      have hz : ((a ^ ((q - 1) / r) : ℕ) : ZMod q) = (1 : ZMod q) := by
        rw [Nat.cast_pow, ← hu_val, hu_div, Units.val_one]
      have hv := congrArg ZMod.val hz
      rw [ZMod.val_natCast, ZMod.val_one] at hv
      exact hv
    have hlt_r : (q - 1) / r < 2 ^ 24 := lt_of_le_of_lt (Nat.div_le_self _ _) hq_lt
    have hne1 := hpowr r hrmem
    rw [powMod_eq a ((q - 1) / r) q hlt_r hq] at hne1
    exact hne1 hmod1
  have hord_dvd_tot : q - 1 ∣ q.totient := by
    rw [← hord_eq, ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  have htot_pos : 0 < q.totient := Nat.totient_pos.mpr (by omega)
  have htot_ge : q - 1 ≤ q.totient := Nat.le_of_dvd htot_pos hord_dvd_tot
  have htot_le : q.totient ≤ q - 1 := Nat.le_sub_one_of_lt (Nat.totient_lt q (by omega))
  exact (Nat.totient_eq_iff_prime (by omega)).mp (le_antisymm htot_le htot_ge)

private inductive PCert : Type
  | trial (q m : ℕ)
  | lucas (q a : ℕ) (fs : List PCert)

private def PCert.val : PCert → ℕ
  | .trial q _ => q
  | .lucas q _ _ => q

private def PCert.check : ℕ → PCert → Bool
  | 0, _ => false
  | _, .trial q m => decide (2 ≤ q) && decide (q < (m + 1) * (m + 1)) && noDivUpTo q m
  | fuel + 1, .lucas q a fs =>
    decide (2 ≤ q) && decide (q - 1 < 2 ^ 24) &&
    (powMod a (q - 1) q == 1) &&
    (stripList (fs.map PCert.val) (q - 1) == 1) &&
    (fs.all fun c => (powMod a ((q - 1) / c.val) q != 1) && PCert.check fuel c)

private lemma PCert.sound : ∀ (fuel : ℕ) (c : PCert), PCert.check fuel c = true → c.val.Prime
  | 0, _, h => by simp [PCert.check] at h
  | fuel + 1, .trial q m, h => by
    unfold PCert.check at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact prime_of_trial h.1.1 h.1.2 h.2
  | fuel + 1, .lucas q a fs, h => by
    unfold PCert.check at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨hq, hqlt⟩, hpow1⟩, hstrip⟩, hfs⟩ := h
    refine prime_of_lucas hq hqlt ?_ hstrip hpow1 ?_
    · intro r hr
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
      exact PCert.sound fuel c (hfs c hc).2
    · intro r hr
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
      exact (hfs c hc).1

private def checkBatch (start : ℕ) : List (ℕ × PCert) → Bool
  | [] => true
  | (x, c) :: rest =>
    let ok := if start ≤ 1 || start == 8 then true
      else decide (0 < x) && decide (x < start) && (c.val == start * x * x + (start - x)) && PCert.check 6 c
    ok && checkBatch (start + 1) rest

private lemma checkBatch_spec (start : ℕ) (ls : List (ℕ × PCert))
    (h : checkBatch start ls = true) (n : ℕ)
    (hlo : start ≤ n) (hhi : n < start + ls.length) (hn1 : 1 < n) (hn8 : n ≠ 8) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (n * x ^ 2 + y).Prime := by
  induction ls generalizing start with
  | nil => simp at hhi; omega
  | cons hd rest ih =>
    rcases hd with ⟨x, c⟩
    unfold checkBatch at h
    simp only [Bool.and_eq_true] at h
    by_cases heq : n = start
    · subst heq
      have hok := h.1
      have hcond : ¬ (decide (n ≤ 1) || (n == 8)) = true := by simp; omega
      rw [if_neg hcond] at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
      obtain ⟨⟨⟨hx0, hxn⟩, hval⟩, hchk⟩ := hok
      refine ⟨x, n - x, hx0, by omega, by omega, ?_⟩
      have hpr := PCert.sound 6 c hchk
      rw [hval] at hpr
      simpa [sq, mul_assoc] using hpr
    · exact ih (start + 1) h.2 (by omega) (by simp at hhi; omega)

private def batch_0 : List (ℕ × PCert) := [
  (0, PCert.trial 2 1),
  (0, PCert.trial 2 1),
  (1, PCert.trial 3 1),
  (1, PCert.trial 5 2),
  (1, PCert.trial 7 2),
  (2, PCert.trial 23 4),
  (1, PCert.trial 11 3),
  (1, PCert.trial 13 3),
  (0, PCert.trial 2 1),
  (1, PCert.trial 17 4),
  (1, PCert.trial 19 4),
  (2, PCert.trial 53 7),
  (1, PCert.trial 23 4),
  (3, PCert.trial 127 11),
  (3, PCert.trial 137 11),
  (1, PCert.trial 29 5),
  (1, PCert.trial 31 5),
  (2, PCert.trial 83 9),
  (5, PCert.trial 463 21),
  (1, PCert.trial 37 6),
  (3, PCert.trial 197 14),
  (1, PCert.trial 41 6),
  (1, PCert.trial 43 6),
  (2, PCert.trial 113 10),
  (1, PCert.trial 47 6),
  (4, PCert.trial 421 20),
  (3, PCert.trial 257 16),
  (1, PCert.trial 53 7),
  (3, PCert.trial 277 16),
  (8, PCert.trial 1877 43),
  (1, PCert.trial 59 7),
  (1, PCert.trial 61 7),
  (3, PCert.trial 317 17),
  (2, PCert.trial 163 12),
  (1, PCert.trial 67 8),
  (2, PCert.trial 173 13),
  (1, PCert.trial 71 8),
  (1, PCert.trial 73 8),
  (5, PCert.trial 983 31),
  (2, PCert.trial 193 13),
  (1, PCert.trial 79 8),
  (5, PCert.trial 1061 32),
  (1, PCert.trial 83 9),
  (4, PCert.trial 727 26),
  (15, PCert.trial 9929 99),
  (1, PCert.trial 89 9),
  (3, PCert.trial 457 21),
  (2, PCert.trial 233 15),
  (7, PCert.trial 2393 48),
  (1, PCert.trial 97 9)
]
private lemma batch_0_ok : checkBatch 0 batch_0 = true := by decide

private def batch_1 : List (ℕ × PCert) := [
  (9, PCert.trial 4091 63),
  (1, PCert.trial 101 10),
  (1, PCert.trial 103 10),
  (2, PCert.trial 263 16),
  (1, PCert.trial 107 10),
  (1, PCert.trial 109 10),
  (3, PCert.trial 557 23),
  (1, PCert.trial 113 10),
  (3, PCert.trial 577 24),
  (2, PCert.trial 293 17),
  (11, PCert.trial 7309 85),
  (3, PCert.trial 607 24),
  (3, PCert.trial 617 24),
  (2, PCert.trial 313 17),
  (1, PCert.trial 127 11),
  (3, PCert.trial 647 25),
  (1, PCert.trial 131 11),
  (6, PCert.trial 2473 49),
  (3, PCert.trial 677 26),
  (1, PCert.trial 137 11),
  (1, PCert.trial 139 11),
  (2, PCert.trial 353 18),
  (5, PCert.trial 1867 43),
  (3, PCert.trial 727 26),
  (21, PCert.lucas 32687 5 [PCert.trial 2 1, PCert.trial 59 7, PCert.trial 277 16]),
  (1, PCert.trial 149 12),
  (1, PCert.trial 151 12),
  (2, PCert.trial 383 19),
  (29, PCert.lucas 65647 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 521 22]),
  (1, PCert.trial 157 12),
  (3, PCert.trial 797 28),
  (4, PCert.trial 1373 37),
  (1, PCert.trial 163 12),
  (3, PCert.trial 827 28),
  (1, PCert.trial 167 12),
  (7, PCert.trial 4243 65),
  (3, PCert.trial 857 29),
  (1, PCert.trial 173 13),
  (3, PCert.trial 877 29),
  (2, PCert.trial 443 21),
  (1, PCert.trial 179 13),
  (1, PCert.trial 181 13),
  (11, PCert.lucas 11213 2 [PCert.trial 2 1, PCert.trial 2803 52]),
  (2, PCert.trial 463 21),
  (3, PCert.trial 937 30),
  (3, PCert.trial 947 30),
  (1, PCert.trial 191 13),
  (1, PCert.trial 193 13),
  (3, PCert.trial 977 31),
  (1, PCert.trial 197 14)
]
private lemma batch_1_ok : checkBatch 50 batch_1 = true := by decide

private def batch_2 : List (ℕ × PCert) := [
  (1, PCert.trial 199 14),
  (2, PCert.trial 503 22),
  (5, PCert.trial 2647 51),
  (4, PCert.trial 1747 41),
  (5, PCert.trial 2699 51),
  (2, PCert.trial 523 22),
  (1, PCert.trial 211 14),
  (5, PCert.trial 2777 52),
  (5, PCert.trial 2803 52),
  (3, PCert.trial 1087 32),
  (3, PCert.trial 1097 33),
  (8, PCert.trial 7207 84),
  (1, PCert.trial 223 14),
  (2, PCert.trial 563 23),
  (1, PCert.trial 227 15),
  (1, PCert.trial 229 15),
  (5, PCert.trial 3011 54),
  (1, PCert.trial 233 15),
  (13, PCert.lucas 20047 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 13 3, PCert.trial 257 16]),
  (2, PCert.trial 593 24),
  (1, PCert.trial 239 15),
  (1, PCert.trial 241 15),
  (3, PCert.trial 1217 34),
  (2, PCert.trial 613 24),
  (3, PCert.trial 1237 35),
  (8, PCert.trial 8117 90),
  (1, PCert.trial 251 15),
  (7, PCert.trial 6343 79),
  (3, PCert.trial 1277 35),
  (1, PCert.trial 257 16),
  (3, PCert.trial 1297 36),
  (2, PCert.trial 653 25),
  (1, PCert.trial 263 16),
  (3, PCert.trial 1327 36),
  (9, PCert.lucas 10979 2 [PCert.trial 2 1, PCert.trial 11 3, PCert.trial 499 22]),
  (1, PCert.trial 269 16),
  (1, PCert.trial 271 16),
  (2, PCert.trial 683 26),
  (5, PCert.trial 3583 59),
  (1, PCert.trial 277 16),
  (9, PCert.lucas 11471 11 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 31 5, PCert.trial 37 6]),
  (1, PCert.trial 281 16),
  (1, PCert.trial 283 16),
  (3, PCert.trial 1427 37),
  (5, PCert.trial 3739 61),
  (3, PCert.trial 1447 38),
  (17, PCert.lucas 42323 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 3023 54]),
  (1, PCert.trial 293 17),
  (7, PCert.trial 7393 85),
  (2, PCert.trial 743 27)
]
private lemma batch_2_ok : checkBatch 100 batch_2 = true := by decide

private def batch_3 : List (ℕ × PCert) := [
  (11, PCert.lucas 18289 13 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 127 11]),
  (6, PCert.trial 5581 74),
  (5, PCert.trial 3947 62),
  (7, PCert.trial 7643 87),
  (1, PCert.trial 307 17),
  (2, PCert.trial 773 27),
  (1, PCert.trial 311 17),
  (1, PCert.trial 313 17),
  (23, PCert.lucas 83717 2 [PCert.trial 2 1, PCert.lucas 20929 7 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 109 10]]),
  (1, PCert.trial 317 17),
  (3, PCert.trial 1597 39),
  (3, PCert.trial 1607 40),
  (7, PCert.trial 8093 89),
  (3, PCert.trial 1627 40),
  (3, PCert.trial 1637 40),
  (2, PCert.trial 823 28),
  (1, PCert.trial 331 18),
  (3, PCert.trial 1667 40),
  (5, PCert.trial 4363 66),
  (1, PCert.trial 337 18),
  (3, PCert.trial 1697 41),
  (2, PCert.trial 853 29),
  (21, PCert.lucas 76003 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 53 7, PCert.trial 239 15]),
  (2, PCert.trial 863 29),
  (1, PCert.trial 347 18),
  (1, PCert.trial 349 18),
  (9, PCert.lucas 14423 5 [PCert.trial 2 1, PCert.trial 7211 84]),
  (1, PCert.trial 353 18),
  (3, PCert.trial 1777 42),
  (3, PCert.trial 1787 42),
  (1, PCert.trial 359 18),
  (6, PCert.trial 6691 81),
  (11, PCert.lucas 22193 3 [PCert.trial 2 1, PCert.trial 19 4, PCert.trial 73 8]),
  (8, PCert.lucas 11887 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 283 16]),
  (1, PCert.trial 367 19),
  (3, PCert.trial 1847 42),
  (5, PCert.trial 4831 69),
  (1, PCert.trial 373 19),
  (3, PCert.trial 1877 43),
  (4, PCert.trial 3209 56),
  (1, PCert.trial 379 19),
  (2, PCert.trial 953 30),
  (1, PCert.trial 383 19),
  (7, PCert.trial 9643 98),
  (5, PCert.trial 5039 70),
  (1, PCert.trial 389 19),
  (9, PCert.lucas 16063 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2677 51]),
  (2, PCert.trial 983 31),
  (13, PCert.lucas 33647 5 [PCert.trial 2 1, PCert.lucas 16823 5 [PCert.trial 2 1, PCert.trial 13 3, PCert.trial 647 25]]),
  (1, PCert.trial 397 19)
]
private lemma batch_3_ok : checkBatch 150 batch_3 = true := by decide

private def batch_4 : List (ℕ × PCert) := [
  (3, PCert.trial 1997 44),
  (1, PCert.trial 401 20),
  (3, PCert.trial 2017 44),
  (2, PCert.trial 1013 31),
  (7, PCert.lucas 10193 3 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 13 3]),
  (1, PCert.trial 409 20),
  (5, PCert.trial 5351 73),
  (2, PCert.trial 1033 32),
  (9, PCert.lucas 17047 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 947 30]),
  (3, PCert.trial 2087 45),
  (1, PCert.trial 419 20),
  (1, PCert.trial 421 20),
  (5, PCert.trial 5507 74),
  (2, PCert.trial 1063 32),
  (3, PCert.trial 2137 46),
  (6, PCert.trial 7949 89),
  (1, PCert.trial 431 20),
  (1, PCert.trial 433 20),
  (15, PCert.lucas 49253 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 1759 41]),
  (2, PCert.trial 1093 33),
  (1, PCert.trial 439 20),
  (2, PCert.trial 1103 33),
  (1, PCert.trial 443 21),
  (12, PCert.lucas 32323 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5387 73]),
  (3, PCert.trial 2237 47),
  (1, PCert.trial 449 21),
  (9, PCert.lucas 18523 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2]),
  (3, PCert.trial 2267 47),
  (5, PCert.trial 5923 76),
  (1, PCert.trial 457 21),
  (3, PCert.trial 2297 47),
  (1, PCert.trial 461 21),
  (1, PCert.trial 463 21),
  (2, PCert.trial 1163 34),
  (1, PCert.trial 467 21),
  (3, PCert.trial 2347 48),
  (3, PCert.trial 2357 48),
  (13, PCert.lucas 40277 2 [PCert.trial 2 1, PCert.lucas 10069 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 839 28]]),
  (3, PCert.trial 2377 48),
  (2, PCert.trial 1193 34),
  (1, PCert.trial 479 21),
  (4, PCert.trial 4093 63),
  (3, PCert.trial 2417 49),
  (2, PCert.trial 1213 34),
  (1, PCert.trial 487 22),
  (2, PCert.trial 1223 34),
  (1, PCert.trial 491 22),
  (3, PCert.trial 2467 49),
  (3, PCert.trial 2477 49),
  (4, PCert.trial 4229 65)
]
private lemma batch_4_ok : checkBatch 200 batch_4 = true := by decide

private def batch_5 : List (ℕ × PCert) := [
  (1, PCert.trial 499 22),
  (5, PCert.trial 6521 80),
  (1, PCert.trial 503 22),
  (4, PCert.trial 4297 65),
  (5, PCert.trial 6599 81),
  (1, PCert.trial 509 22),
  (3, PCert.trial 2557 50),
  (2, PCert.trial 1283 35),
  (5, PCert.trial 6703 81),
  (13, PCert.lucas 44017 11 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 131 11]),
  (23, PCert.lucas 137777 3 [PCert.trial 2 1, PCert.trial 79 8, PCert.trial 109 10]),
  (1, PCert.trial 521 22),
  (1, PCert.trial 523 22),
  (5, PCert.trial 6833 82),
  (13, PCert.lucas 44867 2 [PCert.trial 2 1, PCert.lucas 22433 3 [PCert.trial 2 1, PCert.trial 701 26]]),
  (3, PCert.trial 2647 51),
  (3, PCert.trial 2657 51),
  (11, PCert.lucas 32563 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 67 8]),
  (3, PCert.trial 2677 51),
  (3, PCert.trial 2687 51),
  (13, PCert.lucas 45887 5 [PCert.trial 2 1, PCert.lucas 22943 5 [PCert.trial 2 1, PCert.lucas 11471 11 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 31 5, PCert.trial 37 6]]]),
  (1, PCert.trial 541 23),
  (27, PCert.lucas 198533 2 [PCert.trial 2 1, PCert.lucas 49633 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 11 3, PCert.trial 47 6]]),
  (4, PCert.trial 4637 68),
  (1, PCert.trial 547 23),
  (2, PCert.trial 1373 37),
  (25, PCert.lucas 172751 13 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 691 26]),
  (3, PCert.trial 2767 52),
  (3, PCert.trial 2777 52),
  (1, PCert.trial 557 23),
  (3, PCert.trial 2797 52),
  (6, PCert.lucas 10391 19 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 1039 32]),
  (1, PCert.trial 563 23),
  (7, PCert.lucas 14143 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2357 48]),
  (3, PCert.trial 2837 53),
  (1, PCert.trial 569 23),
  (1, PCert.trial 571 23),
  (2, PCert.trial 1433 37),
  (13, PCert.lucas 48947 2 [PCert.trial 2 1, PCert.lucas 24473 3 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 19 4, PCert.trial 23 4]]),
  (1, PCert.trial 577 24),
  (3, PCert.trial 2897 53),
  (2, PCert.trial 1453 38),
  (3, PCert.trial 2917 54),
  (3, PCert.trial 2927 54),
  (1, PCert.trial 587 24),
  (4, PCert.trial 5011 70),
  (3, PCert.trial 2957 54),
  (1, PCert.trial 593 24),
  (13, PCert.lucas 50647 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 23 4, PCert.trial 367 19]),
  (2, PCert.trial 1493 38)
]
private lemma batch_5_ok : checkBatch 250 batch_5 = true := by decide

private def batch_6 : List (ℕ × PCert) := [
  (1, PCert.trial 599 24),
  (1, PCert.trial 601 24),
  (11, PCert.lucas 36833 3 [PCert.trial 2 1, PCert.trial 1151 33]),
  (4, PCert.trial 5147 71),
  (1, PCert.trial 607 24),
  (2, PCert.trial 1523 39),
  (5, PCert.trial 7951 89),
  (1, PCert.trial 613 24),
  (9, PCert.lucas 25247 5 [PCert.trial 2 1, PCert.trial 13 3, PCert.trial 971 31]),
  (1, PCert.trial 617 24),
  (1, PCert.trial 619 24),
  (2, PCert.trial 1553 39),
  (11, PCert.lucas 38053 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 151 12]),
  (7, PCert.lucas 15643 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 11 3, PCert.trial 79 8]),
  (3, PCert.trial 3137 56),
  (4, PCert.trial 5351 73),
  (1, PCert.trial 631 25),
  (2, PCert.trial 1583 39),
  (5, PCert.trial 8263 90),
  (3, PCert.trial 3187 56),
  (41, PCert.lucas 538199 14 [PCert.trial 2 1, PCert.trial 59 7, PCert.trial 4561 67]),
  (1, PCert.trial 641 25),
  (1, PCert.trial 643 25),
  (2, PCert.trial 1613 40),
  (1, PCert.trial 647 25),
  (4, PCert.trial 5521 74),
  (3, PCert.trial 3257 57),
  (1, PCert.trial 653 25),
  (19, PCert.lucas 118717 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 13 3, PCert.trial 761 27]),
  (8, PCert.lucas 21377 3 [PCert.trial 2 1, PCert.trial 167 12]),
  (1, PCert.trial 659 25),
  (1, PCert.trial 661 25),
  (5, PCert.trial 8627 92),
  (2, PCert.trial 1663 40),
  (7, PCert.lucas 16693 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 13 3, PCert.trial 107 10]),
  (3, PCert.trial 3347 57),
  (5, PCert.trial 8731 93),
  (1, PCert.trial 673 25),
  (5, PCert.trial 8783 93),
  (1, PCert.trial 677 26),
  (7, PCert.lucas 16993 10 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 59 7]),
  (3, PCert.trial 3407 58),
  (1, PCert.trial 683 26),
  (4, PCert.trial 5827 76),
  (11, PCert.lucas 41957 2 [PCert.trial 2 1, PCert.trial 17 4, PCert.trial 617 24]),
  (2, PCert.trial 1723 41),
  (1, PCert.trial 691 26),
  (2, PCert.trial 1733 41),
  (5, PCert.trial 9043 95),
  (6, PCert.lucas 12907 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 239 15])
]
private lemma batch_6_ok : checkBatch 300 batch_6 = true := by decide

private def batch_7 : List (ℕ × PCert) := [
  (11, PCert.lucas 42689 3 [PCert.trial 2 1, PCert.trial 23 4, PCert.trial 29 5]),
  (1, PCert.trial 701 26),
  (3, PCert.trial 3517 59),
  (3, PCert.trial 3527 59),
  (5, PCert.trial 9199 95),
  (1, PCert.trial 709 26),
  (3, PCert.trial 3557 59),
  (2, PCert.trial 1783 42),
  (9, PCert.lucas 29347 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 67 8, PCert.trial 73 8]),
  (8, PCert.lucas 23327 5 [PCert.trial 2 1, PCert.trial 107 10, PCert.trial 109 10]),
  (1, PCert.trial 719 26),
  (3, PCert.trial 3607 60),
  (3, PCert.trial 3617 60),
  (5, PCert.trial 9433 97),
  (1, PCert.trial 727 26),
  (2, PCert.trial 1823 42),
  (5, PCert.trial 9511 97),
  (1, PCert.trial 733 27),
  (3, PCert.trial 3677 60),
  (4, PCert.trial 6269 79),
  (1, PCert.trial 739 27),
  (6, PCert.lucas 13721 3 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 7 2]),
  (1, PCert.trial 743 27),
  (3, PCert.trial 3727 61),
  (5, PCert.trial 9719 98),
  (2, PCert.trial 1873 43),
  (1, PCert.trial 751 27),
  (3, PCert.trial 3767 61),
  (29, PCert.lucas 318247 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 29 5, PCert.trial 31 5, PCert.trial 59 7]),
  (1, PCert.trial 757 27),
  (3, PCert.trial 3797 61),
  (1, PCert.trial 761 27),
  (13, PCert.lucas 64927 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 3607 60]),
  (2, PCert.trial 1913 43),
  (13, PCert.lucas 65267 2 [PCert.trial 2 1, PCert.lucas 32633 3 [PCert.trial 2 1, PCert.trial 4079 63]]),
  (1, PCert.trial 769 27),
  (9, PCert.lucas 31643 2 [PCert.trial 2 1, PCert.trial 13 3, PCert.trial 1217 34]),
  (1, PCert.trial 773 27),
  (3, PCert.trial 3877 62),
  (6, PCert.lucas 14387 2 [PCert.trial 2 1, PCert.trial 7193 84]),
  (11, PCert.lucas 47569 17 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 991 31]),
  (3, PCert.trial 3907 62),
  (3, PCert.trial 3917 62),
  (8, PCert.lucas 25537 10 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 19 4]),
  (1, PCert.trial 787 28),
  (2, PCert.trial 1973 44),
  (7, PCert.lucas 19793 3 [PCert.trial 2 1, PCert.trial 1237 35]),
  (3, PCert.trial 3967 62),
  (5, PCert.lucas 10343 5 [PCert.trial 2 1, PCert.trial 5171 71]),
  (1, PCert.trial 797 28)
]
private lemma batch_7_ok : checkBatch 350 batch_7 = true := by decide

private def batch_8 : List (ℕ × PCert) := [
  (7, PCert.lucas 19993 10 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 17 4]),
  (2, PCert.trial 2003 44),
  (11, PCert.lucas 49033 10 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 227 15]),
  (3, PCert.trial 4027 63),
  (5, PCert.lucas 10499 2 [PCert.trial 2 1, PCert.trial 29 5, PCert.trial 181 13]),
  (1, PCert.trial 809 28),
  (1, PCert.trial 811 28),
  (6, PCert.lucas 15053 2 [PCert.trial 2 1, PCert.trial 53 7, PCert.trial 71 8]),
  (7, PCert.lucas 20393 3 [PCert.trial 2 1, PCert.trial 2549 50]),
  (4, PCert.trial 6949 83),
  (21, PCert.lucas 181199 7 [PCert.trial 2 1, PCert.lucas 90599 11 [PCert.trial 2 1, PCert.trial 97 9, PCert.trial 467 21]]),
  (1, PCert.trial 821 28),
  (1, PCert.trial 823 28),
  (2, PCert.trial 2063 45),
  (1, PCert.trial 827 28),
  (1, PCert.trial 829 28),
  (3, PCert.trial 4157 64),
  (2, PCert.trial 2083 45),
  (3, PCert.trial 4177 64),
  (5, PCert.lucas 10889 3 [PCert.trial 2 1, PCert.trial 1361 36]),
  (1, PCert.trial 839 28),
  (9, PCert.lucas 34513 11 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 719 26]),
  (3, PCert.trial 4217 64),
  (2, PCert.trial 2113 45),
  (7, PCert.lucas 21193 11 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 883 29]),
  (8, PCert.lucas 27617 3 [PCert.trial 2 1, PCert.trial 863 29]),
  (5, PCert.lucas 11071 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 41 6]),
  (1, PCert.trial 853 29),
  (23, PCert.lucas 226817 3 [PCert.trial 2 1, PCert.trial 443 21]),
  (1, PCert.trial 857 29),
  (1, PCert.trial 859 29),
  (2, PCert.trial 2153 46),
  (1, PCert.trial 863 29),
  (3, PCert.trial 4327 65),
  (3, PCert.trial 4337 65),
  (16, PCert.lucas 111779 2 [PCert.trial 2 1, PCert.lucas 55889 3 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 499 22]]),
  (3, PCert.trial 4357 66),
  (12, PCert.lucas 63353 3 [PCert.trial 2 1, PCert.trial 7919 88]),
  (5, PCert.lucas 11383 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 271 16]),
  (1, PCert.trial 877 29),
  (3, PCert.trial 4397 66),
  (1, PCert.trial 881 29),
  (1, PCert.trial 883 29),
  (2, PCert.trial 2213 47),
  (1, PCert.trial 887 29),
  (3, PCert.trial 4447 66),
  (3, PCert.trial 4457 66),
  (5, PCert.lucas 11617 10 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 11 3]),
  (13, PCert.lucas 76147 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 37 6]),
  (2, PCert.trial 2243 47)
]
private lemma batch_8_ok : checkBatch 400 batch_8 = true := by decide

private def batch_9 : List (ℕ × PCert) := [
  (13, PCert.lucas 76487 5 [PCert.trial 2 1, PCert.trial 167 12, PCert.trial 229 15]),
  (3, PCert.trial 4507 67),
  (3, PCert.trial 4517 67),
  (7, PCert.lucas 22643 2 [PCert.trial 2 1, PCert.lucas 11321 3 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 283 16]]),
  (1, PCert.trial 907 30),
  (2, PCert.trial 2273 47),
  (1, PCert.trial 911 30),
  (3, PCert.trial 4567 67),
  (5, PCert.lucas 11903 5 [PCert.trial 2 1, PCert.trial 11 3, PCert.trial 541 23]),
  (2, PCert.trial 2293 47),
  (1, PCert.trial 919 30),
  (5, PCert.lucas 11981 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 599 24]),
  (5, PCert.lucas 12007 13 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 23 4, PCert.trial 29 5]),
  (4, PCert.trial 7867 88),
  (3, PCert.trial 4637 68),
  (1, PCert.trial 929 30),
  (3, PCert.trial 4657 68),
  (2, PCert.trial 2333 48),
  (5, PCert.lucas 12163 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2027 45]),
  (1, PCert.trial 937 30),
  (11, PCert.lucas 57329 3 [PCert.trial 2 1, PCert.trial 3583 59]),
  (1, PCert.trial 941 30),
  (7, PCert.lucas 23593 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 983 31]),
  (17, PCert.lucas 137153 3 [PCert.trial 2 1, PCert.trial 2143 46]),
  (1, PCert.trial 947 30),
  (6, PCert.lucas 17569 11 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 61 7]),
  (9, PCert.lucas 39023 5 [PCert.trial 2 1, PCert.trial 109 10, PCert.trial 179 13]),
  (1, PCert.trial 953 30),
  (7, PCert.lucas 23893 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 11 3, PCert.trial 181 13]),
  (2, PCert.trial 2393 48),
  (7, PCert.lucas 23993 3 [PCert.trial 2 1, PCert.trial 2999 54]),
  (6, PCert.lucas 17791 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 593 24]),
  (3, PCert.trial 4817 69),
  (5, PCert.lucas 12553 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 523 22]),
  (1, PCert.trial 967 31),
  (2, PCert.trial 2423 49),
  (1, PCert.trial 971 31),
  (6, PCert.lucas 18013 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 19 4, PCert.trial 79 8]),
  (3, PCert.trial 4877 69),
  (1, PCert.trial 977 31),
  (39, PCert.lucas 745741 7 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 1381 37]),
  (8, PCert.lucas 31907 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 43 6, PCert.trial 53 7]),
  (1, PCert.trial 983 31),
  (4, PCert.trial 8377 91),
  (3, PCert.trial 4937 70),
  (2, PCert.trial 2473 49),
  (1, PCert.trial 991 31),
  (3, PCert.trial 4967 70),
  (43, PCert.lucas 921257 5 [PCert.trial 2 1, PCert.trial 7 2, PCert.lucas 16451 7 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 7 2, PCert.trial 47 6]]),
  (1, PCert.trial 997 31)
]
private lemma batch_9_ok : checkBatch 450 batch_9 = true := by decide

private def batch_10 : List (ℕ × PCert) := [
  (17, PCert.lucas 144983 5 [PCert.trial 2 1, PCert.trial 71 8, PCert.trial 1021 31]),
  (2, PCert.trial 2503 50),
  (15, PCert.lucas 113437 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 23 4, PCert.trial 137 11]),
  (8, PCert.lucas 32687 5 [PCert.trial 2 1, PCert.trial 59 7, PCert.trial 277 16]),
  (5, PCert.lucas 13099 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 37 6, PCert.trial 59 7]),
  (1, PCert.trial 1009 31),
  (5, PCert.lucas 13151 13 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 263 16]),
  (1, PCert.trial 1013 31),
  (3, PCert.trial 5077 71),
  (2, PCert.trial 2543 50),
  (1, PCert.trial 1019 31),
  (1, PCert.trial 1021 31),
  (21, PCert.lucas 226283 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 2309 48]),
  (7, PCert.lucas 25643 2 [PCert.trial 2 1, PCert.lucas 12821 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 641 25]]),
  (7, PCert.lucas 25693 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2141 46]),
  (3, PCert.trial 5147 71),
  (1, PCert.trial 1031 32),
  (1, PCert.trial 1033 32),
  (5, PCert.lucas 13463 5 [PCert.trial 2 1, PCert.trial 53 7, PCert.trial 127 11]),
  (2, PCert.trial 2593 50),
  (1, PCert.trial 1039 32),
  (8, PCert.lucas 33857 3 [PCert.trial 2 1, PCert.trial 23 4]),
  (5, PCert.lucas 13567 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 17 4, PCert.trial 19 4]),
  (3, PCert.trial 5227 72),
  (3, PCert.trial 5237 72),
  (1, PCert.trial 1049 32),
  (1, PCert.trial 1051 32),
  (2, PCert.trial 2633 51),
  (5, PCert.lucas 13723 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2287 47]),
  (10, PCert.lucas 53419 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 29 5, PCert.trial 307 17]),
  (3, PCert.trial 5297 72),
  (1, PCert.trial 1061 32),
  (1, PCert.trial 1063 32),
  (2, PCert.trial 2663 51),
  (5, PCert.lucas 13879 6 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 257 16]),
  (1, PCert.trial 1069 32),
  (5, PCert.lucas 13931 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 7 2, PCert.trial 199 14]),
  (2, PCert.trial 2683 51),
  (7, PCert.lucas 26893 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 83 9]),
  (2, PCert.trial 2693 51),
  (7, PCert.lucas 26993 3 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 241 15]),
  (3, PCert.trial 5407 73),
  (3, PCert.trial 5417 73),
  (2, PCert.trial 2713 52),
  (1, PCert.trial 1087 32),
  (14, PCert.lucas 107351 19 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 19 4, PCert.trial 113 10]),
  (1, PCert.trial 1091 33),
  (1, PCert.trial 1093 33),
  (3, PCert.trial 5477 74),
  (1, PCert.trial 1097 33)
]
private lemma batch_10_ok : checkBatch 500 batch_10 = true := by decide

private def batch_11 : List (ℕ × PCert) := [
  (13, PCert.lucas 93487 6 [PCert.trial 2 1, PCert.trial 3 1, PCert.lucas 15581 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 19 4, PCert.trial 41 6]]),
  (2, PCert.trial 2753 52),
  (1, PCert.trial 1103 33),
  (3, PCert.trial 5527 74),
  (11, PCert.lucas 67577 3 [PCert.trial 2 1, PCert.trial 8447 91]),
  (1, PCert.trial 1109 33),
  (3, PCert.trial 5557 74),
  (11, PCert.lucas 67943 5 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 23 4, PCert.trial 211 14]),
  (5, PCert.lucas 14503 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2417 49]),
  (1, PCert.trial 1117 33),
  (27, PCert.lucas 408773 3 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 13 3, PCert.trial 1123 33]),
  (2, PCert.trial 2803 52),
  (1, PCert.trial 1123 33),
  (5, PCert.lucas 14633 3 [PCert.trial 2 1, PCert.trial 31 5, PCert.trial 59 7]),
  (17, PCert.lucas 163543 6 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 97 9, PCert.trial 281 16]),
  (1, PCert.trial 1129 33),
  (3, PCert.trial 5657 75),
  (2, PCert.trial 2833 53),
  (7, PCert.lucas 28393 15 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 13 3]),
  (2, PCert.trial 2843 53),
  (7, PCert.lucas 28493 2 [PCert.trial 2 1, PCert.trial 17 4, PCert.trial 419 20]),
  (6, PCert.lucas 21121 19 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 11 3]),
  (3, PCert.trial 5717 75),
  (7, PCert.lucas 28643 2 [PCert.trial 2 1, PCert.lucas 14321 3 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 179 13]]),
  (3, PCert.trial 5737 75),
  (6, PCert.lucas 21269 2 [PCert.trial 2 1, PCert.trial 13 3, PCert.trial 409 20]),
  (1, PCert.trial 1151 33),
  (1, PCert.trial 1153 33),
  (9, PCert.lucas 47387 2 [PCert.trial 2 1, PCert.trial 19 4, PCert.trial 29 5, PCert.trial 43 6]),
  (4, PCert.trial 9839 99),
  (43, PCert.lucas 1072957 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.lucas 89413 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7451 86]]),
  (2, PCert.trial 2903 53),
  (1, PCert.trial 1163 34),
  (3, PCert.trial 5827 76),
  (11, PCert.lucas 71237 2 [PCert.trial 2 1, PCert.trial 11 3, PCert.trial 1619 40]),
  (4, PCert.trial 9941 99),
  (1, PCert.trial 1171 34),
  (3, PCert.trial 5867 76),
  (17, PCert.lucas 170503 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 157 12, PCert.trial 181 13]),
  (4, PCert.lucas 10009 11 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 139 11]),
  (3, PCert.trial 5897 76),
  (1, PCert.trial 1181 34),
  (21, PCert.lucas 261643 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.lucas 43607 5 [PCert.trial 2 1, PCert.lucas 21803 2 [PCert.trial 2 1, PCert.trial 11 3, PCert.trial 991 31]]]),
  (2, PCert.trial 2963 54),
  (1, PCert.trial 1187 34),
  (4, PCert.lucas 10111 12 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 337 18]),
  (11, PCert.lucas 72701 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 727 26]),
  (1, PCert.trial 1193 34),
  (43, PCert.lucas 1106257 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 19 4, PCert.trial 1213 34]),
  (3, PCert.trial 5987 77)
]
private lemma batch_11_ok : checkBatch 550 batch_11 = true := by decide

private def batch_12 : List (ℕ × PCert) := [
  (11, PCert.lucas 73189 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 19 4, PCert.trial 107 10]),
  (1, PCert.trial 1201 34),
  (5, PCert.lucas 15647 5 [PCert.trial 2 1, PCert.trial 7823 88]),
  (4, PCert.lucas 10247 5 [PCert.trial 2 1, PCert.trial 47 6, PCert.trial 109 10]),
  (3, PCert.trial 6037 77),
  (2, PCert.trial 3023 54),
  (7, PCert.lucas 30293 2 [PCert.trial 2 1, PCert.trial 7573 87]),
  (1, PCert.trial 1213 34),
  (5, PCert.lucas 15803 2 [PCert.trial 2 1, PCert.trial 7901 88]),
  (1, PCert.trial 1217 34),
  (7, PCert.lucas 30493 6 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 11 3]),
  (5, PCert.lucas 15881 3 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 397 19]),
  (1, PCert.trial 1223 34),
  (7, PCert.lucas 30643 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5107 71]),
  (5, PCert.lucas 15959 11 [PCert.trial 2 1, PCert.trial 79 8, PCert.trial 101 10]),
  (1, PCert.trial 1229 35),
  (1, PCert.trial 1231 35),
  (2, PCert.trial 3083 55),
  (5, PCert.lucas 16063 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2677 51]),
  (1, PCert.trial 1237 35),
  (3, PCert.trial 6197 78),
  (5, PCert.lucas 16141 6 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 269 16]),
  (3, PCert.trial 6217 78),
  (5, PCert.lucas 16193 5 [PCert.trial 2 1, PCert.trial 11 3, PCert.trial 23 4]),
  (7, PCert.lucas 31193 5 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 557 23]),
  (1, PCert.trial 1249 35),
  (3, PCert.trial 6257 79),
  (10, PCert.lucas 63317 2 [PCert.trial 2 1, PCert.trial 11 3, PCert.trial 1439 37]),
  (3, PCert.trial 6277 79),
  (3, PCert.trial 6287 79),
  (1, PCert.trial 1259 35),
  (4, PCert.lucas 10723 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 1787 42]),
  (3, PCert.trial 6317 79),
  (2, PCert.trial 3163 56),
  (3, PCert.trial 6337 79),
  (17, PCert.lucas 184133 2 [PCert.trial 2 1, PCert.trial 13 3, PCert.trial 3541 59]),
  (7, PCert.lucas 31793 3 [PCert.trial 2 1, PCert.trial 1987 44]),
  (3, PCert.trial 6367 79),
  (15, PCert.lucas 144173 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 19 4, PCert.trial 271 16]),
  (1, PCert.trial 1277 35),
  (1, PCert.trial 1279 35),
  (2, PCert.trial 3203 56),
  (1, PCert.trial 1283 35),
  (3, PCert.trial 6427 80),
  (17, PCert.lucas 186743 5 [PCert.trial 2 1, PCert.lucas 93371 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 9337 96]]),
  (1, PCert.trial 1289 35),
  (1, PCert.trial 1291 35),
  (18, PCert.lucas 210257 3 [PCert.trial 2 1, PCert.trial 17 4, PCert.trial 773 27]),
  (5, PCert.lucas 16843 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 401 20]),
  (1, PCert.trial 1297 36)
]
private lemma batch_12_ok : checkBatch 600 batch_12 = true := by decide

private def batch_13 : List (ℕ × PCert) := [
  (17, PCert.lucas 188483 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.lucas 13463 5 [PCert.trial 2 1, PCert.trial 53 7, PCert.trial 127 11]]),
  (1, PCert.trial 1301 36),
  (1, PCert.trial 1303 36),
  (8, PCert.lucas 42437 2 [PCert.trial 2 1, PCert.trial 103 10]),
  (1, PCert.trial 1307 36),
  (3, PCert.trial 6547 80),
  (9, PCert.lucas 53783 5 [PCert.trial 2 1, PCert.lucas 26891 6 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 2689 51]]),
  (5, PCert.lucas 17077 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 1423 37]),
  (3, PCert.trial 6577 81),
  (11, PCert.lucas 80387 2 [PCert.trial 2 1, PCert.lucas 40193 3 [PCert.trial 2 1, PCert.trial 157 12]]),
  (1, PCert.trial 1319 36),
  (1, PCert.trial 1321 36),
  (5, PCert.lucas 17207 5 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 1229 35]),
  (2, PCert.trial 3313 57),
  (1, PCert.trial 1327 36),
  (2, PCert.trial 3323 57),
  (71, PCert.lucas 3357901 11 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 7 2, PCert.trial 13 3, PCert.trial 41 6]),
  (7, PCert.lucas 33343 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5557 74]),
  (9, PCert.lucas 54767 5 [PCert.trial 2 1, PCert.trial 139 11, PCert.trial 197 14]),
  (2, PCert.trial 3343 57),
  (7, PCert.lucas 33493 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2791 52]),
  (6, PCert.lucas 24821 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 17 4, PCert.trial 73 8]),
  (5, PCert.lucas 17467 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 41 6, PCert.trial 71 8]),
  (4, PCert.lucas 11437 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 953 30]),
  (3, PCert.trial 6737 82),
  (2, PCert.trial 3373 58),
  (31, PCert.lucas 650281 29 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 5419 73]),
  (5, PCert.lucas 17597 2 [PCert.trial 2 1, PCert.trial 53 7, PCert.trial 83 9]),
  (5, PCert.lucas 17623 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 11 3, PCert.trial 89 9]),
  (6, PCert.lucas 25117 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 13 3, PCert.trial 23 4]),
  (41, PCert.lucas 1143719 11 [PCert.trial 2 1, PCert.trial 193 13, PCert.trial 2963 54]),
  (1, PCert.trial 1361 36),
  (21, PCert.lucas 301423 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 11 3, PCert.trial 4567 67]),
  (2, PCert.trial 3413 58),
  (1, PCert.trial 1367 36),
  (6, PCert.lucas 25339 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 41 6, PCert.trial 103 10]),
  (3, PCert.trial 6857 82),
  (1, PCert.trial 1373 37),
  (15, PCert.lucas 155473 11 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 41 6, PCert.trial 79 8]),
  (5, PCert.lucas 17909 2 [PCert.trial 2 1, PCert.trial 11 3, PCert.trial 37 6]),
  (53, PCert.lucas 1938847 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 13 3, PCert.trial 53 7, PCert.trial 67 8]),
  (1, PCert.trial 1381 37),
  (3, PCert.trial 6917 83),
  (2, PCert.trial 3463 58),
  (7, PCert.lucas 34693 6 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 59 7]),
  (3, PCert.trial 6947 83),
  (17, PCert.lucas 201823 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.lucas 33637 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2803 52]]),
  (3, PCert.trial 6967 83),
  (3, PCert.trial 6977 83),
  (5, PCert.lucas 18169 11 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 757 27])
]
private lemma batch_13_ok : checkBatch 650 batch_13 = true := by decide

private def batch_14 : List (ℕ × PCert) := [
  (1, PCert.trial 1399 37),
  (6, PCert.lucas 25931 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 2593 50]),
  (17, PCert.lucas 203563 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 43 6, PCert.trial 263 16]),
  (3, PCert.trial 7027 83),
  (9, PCert.lucas 57719 7 [PCert.trial 2 1, PCert.lucas 28859 2 [PCert.trial 2 1, PCert.trial 47 6, PCert.trial 307 17]]),
  (1, PCert.trial 1409 37),
  (3, PCert.trial 7057 84),
  (2, PCert.trial 3533 59),
  (7, PCert.lucas 35393 3 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 79 8]),
  (4, PCert.lucas 12049 13 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 251 15]),
  (9, PCert.lucas 58211 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 5821 76]),
  (5, PCert.lucas 18481 13 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 7 2, PCert.trial 11 3]),
  (1, PCert.trial 1423 37),
  (3, PCert.trial 7127 84),
  (1, PCert.trial 1427 37),
  (1, PCert.trial 1429 37),
  (39, PCert.lucas 1089713 3 [PCert.trial 2 1, PCert.trial 13 3, PCert.trial 31 5]),
  (1, PCert.trial 1433 37),
  (3, PCert.trial 7177 84),
  (2, PCert.trial 3593 59),
  (1, PCert.trial 1439 37),
  (3, PCert.trial 7207 84),
  (51, PCert.lucas 1878593 3 [PCert.trial 2 1, PCert.trial 149 12, PCert.trial 197 14]),
  (2, PCert.trial 3613 60),
  (1, PCert.trial 1447 38),
  (2, PCert.trial 3623 60),
  (1, PCert.trial 1451 38),
  (1, PCert.trial 1453 38),
  (15, PCert.lucas 164513 3 [PCert.trial 2 1, PCert.trial 53 7, PCert.trial 97 9]),
  (2, PCert.trial 3643 60),
  (1, PCert.trial 1459 38),
  (3, PCert.trial 7307 85),
  (11, PCert.lucas 89293 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 1063 32]),
  (4, PCert.lucas 12457 10 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 173 13]),
  (5, PCert.lucas 19079 7 [PCert.trial 2 1, PCert.trial 9539 97]),
  (2, PCert.trial 3673 60),
  (1, PCert.trial 1471 38),
  (5, PCert.lucas 19157 2 [PCert.trial 2 1, PCert.trial 4789 69]),
  (5, PCert.lucas 19183 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 23 4, PCert.trial 139 11]),
  (6, PCert.lucas 27337 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 17 4, PCert.trial 67 8]),
  (21, PCert.lucas 327059 2 [PCert.trial 2 1, PCert.trial 43 6, PCert.trial 3803 61]),
  (1, PCert.trial 1481 38),
  (1, PCert.trial 1483 38),
  (9, PCert.lucas 60917 2 [PCert.trial 2 1, PCert.trial 97 9, PCert.trial 157 12]),
  (1, PCert.trial 1487 38),
  (1, PCert.trial 1489 38),
  (3, PCert.trial 7457 86),
  (1, PCert.trial 1493 38),
  (3, PCert.trial 7477 86),
  (3, PCert.trial 7487 86)
]
private lemma batch_14_ok : checkBatch 700 batch_14 = true := by decide

private def batch_15 : List (ℕ × PCert) := [
  (1, PCert.trial 1499 38),
  (3, PCert.trial 7507 86),
  (3, PCert.trial 7517 86),
  (7, PCert.lucas 37643 2 [PCert.trial 2 1, PCert.trial 11 3, PCert.trial 29 5, PCert.trial 59 7]),
  (3, PCert.trial 7537 86),
  (3, PCert.trial 7547 86),
  (1, PCert.trial 1511 38),
  (13, PCert.lucas 128677 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.lucas 10723 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 1787 42]]),
  (3, PCert.trial 7577 87),
  (2, PCert.trial 3793 61),
  (7, PCert.lucas 37993 10 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 1583 39]),
  (2, PCert.trial 3803 61),
  (1, PCert.trial 1523 39),
  (4, PCert.lucas 12967 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2161 46]),
  (9, PCert.lucas 62639 11 [PCert.trial 2 1, PCert.lucas 31319 7 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 2237 47]]),
  (2, PCert.trial 3823 61),
  (1, PCert.trial 1531 39),
  (2, PCert.trial 3833 61),
  (5, PCert.lucas 19963 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 1109 33]),
  (3, PCert.trial 7687 87),
  (9, PCert.lucas 63131 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 59 7, PCert.trial 107 10]),
  (2, PCert.trial 3853 62),
  (1, PCert.trial 1543 39),
  (2, PCert.trial 3863 62),
  (7, PCert.lucas 38693 2 [PCert.trial 2 1, PCert.trial 17 4, PCert.trial 569 23]),
  (1, PCert.trial 1549 39),
  (3, PCert.trial 7757 88),
  (1, PCert.trial 1553 39),
  (13, PCert.lucas 132247 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 31 5, PCert.trial 79 8]),
  (5, PCert.lucas 20249 3 [PCert.trial 2 1, PCert.trial 2531 50]),
  (1, PCert.trial 1559 39),
  (7, PCert.lucas 39043 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 241 15]),
  (3, PCert.trial 7817 88),
  (5, PCert.lucas 20353 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 53 7]),
  (1, PCert.trial 1567 39),
  (2, PCert.trial 3923 62),
  (1, PCert.trial 1571 39),
  (3, PCert.trial 7867 88),
  (3, PCert.trial 7877 88),
  (2, PCert.trial 3943 62),
  (1, PCert.trial 1579 39),
  (3, PCert.trial 7907 88),
  (1, PCert.trial 1583 39),
  (3, PCert.trial 7927 89),
  (3, PCert.trial 7937 89),
  (11, PCert.lucas 96979 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 2309 48]),
  (21, PCert.lucas 351811 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 1303 36]),
  (5, PCert.lucas 20717 2 [PCert.trial 2 1, PCert.trial 5179 71]),
  (5, PCert.lucas 20743 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 3457 58]),
  (1, PCert.trial 1597 39)
]
private lemma batch_15_ok : checkBatch 750 batch_15 = true := by decide

private def batch_16 : List (ℕ × PCert) := [
  (23, PCert.lucas 423977 3 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 67 8, PCert.trial 113 10]),
  (1, PCert.trial 1601 40),
  (3, PCert.trial 8017 89),
  (2, PCert.trial 4013 63),
  (1, PCert.trial 1607 40),
  (1, PCert.trial 1609 40),
  (9, PCert.lucas 66083 2 [PCert.trial 2 1, PCert.trial 19 4, PCert.trial 37 6, PCert.trial 47 6]),
  (1, PCert.trial 1613 40),
  (15, PCert.lucas 182593 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 317 17]),
  (3, PCert.trial 8087 89),
  (1, PCert.trial 1619 40),
  (1, PCert.trial 1621 40),
  (3, PCert.trial 8117 90),
  (8, PCert.lucas 52837 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 17 4, PCert.trial 37 6]),
  (1, PCert.trial 1627 40),
  (2, PCert.trial 4073 63),
  (5, PCert.lucas 21211 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 7 2, PCert.trial 101 10]),
  (3, PCert.trial 8167 90),
  (17, PCert.lucas 237203 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.lucas 16943 5 [PCert.trial 2 1, PCert.trial 43 6, PCert.trial 197 14]]),
  (1, PCert.trial 1637 40),
  (7, PCert.lucas 40993 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 61 7]),
  (5, PCert.lucas 21341 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 11 3, PCert.trial 97 9]),
  (17, PCert.lucas 238363 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.lucas 39727 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2207 46]]),
  (7, PCert.lucas 41143 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 6857 82]),
  (3, PCert.trial 8237 90),
  (7, PCert.lucas 41243 2 [PCert.trial 2 1, PCert.trial 17 4, PCert.trial 1213 34]),
  (9, PCert.lucas 67723 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.lucas 11287 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 11 3, PCert.trial 19 4]]),
  (2, PCert.trial 4133 64),
  (5, PCert.lucas 21523 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 17 4, PCert.trial 211 14]),
  (1, PCert.trial 1657 40),
  (3, PCert.trial 8297 91),
  (2, PCert.trial 4153 64),
  (1, PCert.trial 1663 40),
  (29, PCert.lucas 701357 2 [PCert.trial 2 1, PCert.trial 67 8, PCert.trial 2617 51]),
  (1, PCert.trial 1667 40),
  (1, PCert.trial 1669 40),
  (9, PCert.lucas 68543 5 [PCert.trial 2 1, PCert.trial 43 6, PCert.trial 797 28]),
  (5, PCert.lucas 21757 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 37 6]),
  (3, PCert.trial 8377 91),
  (3, PCert.trial 8387 91),
  (13, PCert.lucas 142787 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 31 5, PCert.trial 47 6]),
  (4, PCert.lucas 14293 6 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 397 19]),
  (27, PCert.lucas 614633 3 [PCert.trial 2 1, PCert.lucas 76829 2 [PCert.trial 2 1, PCert.lucas 19207 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 11 3, PCert.trial 97 9]]]),
  (4, PCert.lucas 14327 5 [PCert.trial 2 1, PCert.trial 13 3, PCert.trial 19 4, PCert.trial 29 5]),
  (7, PCert.lucas 42193 15 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 293 17]),
  (3, PCert.trial 8447 91),
  (5, PCert.lucas 21991 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 733 27]),
  (1, PCert.trial 1693 41),
  (23, PCert.lucas 449417 3 [PCert.trial 2 1, PCert.trial 11 3, PCert.trial 5107 71]),
  (1, PCert.trial 1697 41)
]
private lemma batch_16_ok : checkBatch 800 batch_16 = true := by decide

private def batch_17 : List (ℕ × PCert) := [
  (1, PCert.trial 1699 41),
  (2, PCert.trial 4253 65),
  (5, PCert.lucas 22147 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 3691 60]),
  (3, PCert.trial 8527 92),
  (3, PCert.trial 8537 92),
  (1, PCert.trial 1709 41),
  (7, PCert.lucas 42793 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 1783 42]),
  (2, PCert.trial 4283 65),
  (5, PCert.lucas 22303 6 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 59 7]),
  (7, PCert.lucas 42943 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 17 4, PCert.trial 421 20]),
  (3, PCert.trial 8597 92),
  (1, PCert.trial 1721 41),
  (1, PCert.trial 1723 41),
  (3, PCert.trial 8627 92),
  (11, PCert.lucas 105397 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 8783 93]),
  (3, PCert.trial 8647 92),
  (5, PCert.lucas 22511 11 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 2251 47]),
  (1, PCert.trial 1733 41),
  (3, PCert.trial 8677 93),
  (8, PCert.lucas 56477 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 2017 44]),
  (11, PCert.lucas 106129 23 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 11 3, PCert.trial 67 8]),
  (1, PCert.trial 1741 41),
  (11, PCert.lucas 106373 5 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 29 5, PCert.trial 131 11]),
  (2, PCert.trial 4363 66),
  (1, PCert.trial 1747 41),
  (2, PCert.trial 4373 66),
  (7, PCert.lucas 43793 3 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 17 4, PCert.trial 23 4]),
  (1, PCert.trial 1753 41),
  (9, PCert.lucas 71987 2 [PCert.trial 2 1, PCert.lucas 35993 3 [PCert.trial 2 1, PCert.trial 11 3, PCert.trial 409 20]]),
  (4, PCert.lucas 14939 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 11 3, PCert.trial 97 9]),
  (1, PCert.trial 1759 41),
  (3, PCert.trial 8807 93),
  (17, PCert.lucas 255763 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 13 3, PCert.trial 1093 33]),
  (13, PCert.lucas 150097 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 53 7, PCert.trial 59 7]),
  (3, PCert.trial 8837 94),
  (2, PCert.trial 4423 66),
  (7, PCert.lucas 44293 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 3691 60]),
  (3, PCert.trial 8867 94),
  (17, PCert.lucas 257503 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 6131 78]),
  (1, PCert.trial 1777 42),
  (23, PCert.lucas 471677 2 [PCert.trial 2 1, PCert.trial 37 6, PCert.trial 3187 56]),
  (7, PCert.lucas 44543 5 [PCert.trial 2 1, PCert.lucas 22271 7 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 17 4, PCert.trial 131 11]]),
  (1, PCert.trial 1783 42),
  (2, PCert.trial 4463 66),
  (1, PCert.trial 1787 42),
  (1, PCert.trial 1789 42),
  (5, PCert.lucas 23291 6 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 17 4, PCert.trial 137 11]),
  (2, PCert.trial 4483 66),
  (7, PCert.lucas 44893 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 29 5, PCert.trial 43 6]),
  (2, PCert.trial 4493 67)
]
private lemma batch_17_ok : checkBatch 850 batch_17 = true := by decide

private def batch_18 : List (ℕ × PCert) := [
  (11, PCert.lucas 109789 10 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 1307 36]),
  (1, PCert.trial 1801 42),
  (5, PCert.lucas 23447 5 [PCert.trial 2 1, PCert.trial 19 4, PCert.trial 617 24]),
  (2, PCert.trial 4513 67),
  (51, PCert.lucas 2352157 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 31 5, PCert.trial 6323 79]),
  (2, PCert.trial 4523 67),
  (1, PCert.trial 1811 42),
  (3, PCert.trial 9067 95),
  (5, PCert.lucas 23603 2 [PCert.trial 2 1, PCert.lucas 11801 3 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 59 7]]),
  (5, PCert.lucas 23629 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 11 3, PCert.trial 179 13]),
  (9, PCert.lucas 74611 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 829 28]),
  (8, PCert.lucas 59207 5 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 4229 65]),
  (1, PCert.trial 1823 42),
  (3, PCert.trial 9127 95),
  (3, PCert.trial 9137 95),
  (4, PCert.lucas 15551 7 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 311 17]),
  (1, PCert.trial 1831 42),
  (2, PCert.trial 4583 67),
  (7, PCert.lucas 45893 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 11 3, PCert.trial 149 12]),
  (3, PCert.trial 9187 95),
  (9, PCert.lucas 75431 19 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 19 4, PCert.trial 397 19]),
  (2, PCert.trial 4603 67),
  (7, PCert.lucas 46093 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 23 4, PCert.trial 167 12]),
  (3, PCert.trial 9227 96),
  (1, PCert.trial 1847 42),
  (28, PCert.lucas 726097 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 2161 46]),
  (3, PCert.trial 9257 96),
  (5, PCert.lucas 24097 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 251 15]),
  (3, PCert.trial 9277 96),
  (2, PCert.trial 4643 68),
  (17, PCert.lucas 269683 7 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 6421 80]),
  (1, PCert.trial 1861 43),
  (21, PCert.lucas 411923 2 [PCert.trial 2 1, PCert.trial 7 2, PCert.lucas 29423 5 [PCert.trial 2 1, PCert.trial 47 6, PCert.trial 313 17]]),
  (2, PCert.trial 4663 68),
  (1, PCert.trial 1867 43),
  (2, PCert.trial 4673 68),
  (1, PCert.trial 1871 43),
  (1, PCert.trial 1873 43),
  (3, PCert.trial 9377 96),
  (1, PCert.trial 1877 43),
  (1, PCert.trial 1879 43),
  (2, PCert.trial 4703 68),
  (7, PCert.lucas 47093 2 [PCert.trial 2 1, PCert.trial 61 7, PCert.trial 193 13]),
  (7, PCert.lucas 47143 6 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 97 9]),
  (3, PCert.trial 9437 97),
  (1, PCert.trial 1889 43),
  (7, PCert.lucas 47293 6 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 563 23]),
  (2, PCert.trial 4733 68),
  (37, PCert.lucas 1298723 2 [PCert.trial 2 1, PCert.lucas 649361 3 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 8117 90]]),
  (6, PCert.lucas 35107 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5851 76])
]
private lemma batch_18_ok : checkBatch 900 batch_18 = true := by decide

private def batch_19 : List (ℕ × PCert) := [
  (3, PCert.trial 9497 97),
  (1, PCert.trial 1901 43),
  (25, PCert.lucas 595927 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.lucas 33107 2 [PCert.trial 2 1, PCert.lucas 16553 3 [PCert.trial 2 1, PCert.trial 2069 45]]]),
  (9, PCert.lucas 78137 3 [PCert.trial 2 1, PCert.trial 9767 98]),
  (1, PCert.trial 1907 43),
  (3, PCert.trial 9547 97),
  (5, PCert.lucas 24851 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 7 2, PCert.trial 71 8]),
  (1, PCert.trial 1913 43),
  (13, PCert.lucas 162847 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 83 9, PCert.trial 109 10]),
  (2, PCert.trial 4793 69),
  (11, PCert.lucas 117109 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 3253 57]),
  (4, PCert.lucas 16333 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 1361 36]),
  (11, PCert.lucas 117353 3 [PCert.trial 2 1, PCert.lucas 14669 2 [PCert.trial 2 1, PCert.trial 19 4, PCert.trial 193 13]]),
  (2, PCert.trial 4813 69),
  (7, PCert.lucas 48193 7 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 251 15]),
  (24, PCert.lucas 556781 2 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 7 2, PCert.trial 41 6, PCert.trial 97 9]),
  (1, PCert.trial 1931 43),
  (1, PCert.trial 1933 43),
  (3, PCert.trial 9677 98),
  (5, PCert.lucas 25189 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2099 45]),
  (3, PCert.trial 9697 98),
  (9, PCert.lucas 79613 2 [PCert.trial 2 1, PCert.trial 13 3, PCert.trial 1531 39]),
  (7, PCert.lucas 48593 3 [PCert.trial 2 1, PCert.trial 3037 55]),
  (9, PCert.lucas 79777 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 277 16]),
  (21, PCert.lucas 430487 7 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 97 9, PCert.trial 317 17]),
  (1, PCert.trial 1949 44),
  (1, PCert.trial 1951 44),
  (3, PCert.trial 9767 98),
  (5, PCert.lucas 25423 3 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 19 4, PCert.trial 223 14]),
  (3, PCert.trial 9787 98),
  (11, PCert.lucas 119549 2 [PCert.trial 2 1, PCert.trial 11 3, PCert.trial 13 3, PCert.trial 19 4]),
  (2, PCert.trial 4903 70),
  (3, PCert.trial 9817 99),
  (23, PCert.lucas 520967 5 [PCert.trial 2 1, PCert.lucas 260483 2 [PCert.trial 2 1, PCert.lucas 130241 3 [PCert.trial 2 1, PCert.trial 5 2, PCert.trial 11 3, PCert.trial 37 6]]]),
  (5, PCert.lucas 25579 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2, PCert.trial 29 5]),
  (4, PCert.lucas 16741 6 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2, PCert.trial 31 5]),
  (3, PCert.trial 9857 99),
  (1, PCert.trial 1973 44),
  (7, PCert.lucas 49393 5 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 7 2]),
  (2, PCert.trial 4943 70),
  (1, PCert.trial 1979 44),
  (3, PCert.trial 9907 99),
  (11, PCert.lucas 121013 2 [PCert.trial 2 1, PCert.lucas 30253 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 2521 50]]),
  (28, PCert.lucas 779477 2 [PCert.trial 2 1, PCert.lucas 194869 22 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5413 73]]),
  (1, PCert.trial 1987 44),
  (2, PCert.trial 4973 70),
  (11, PCert.lucas 121501 2 [PCert.trial 2 1, PCert.trial 3 1, PCert.trial 5 2]),
  (1, PCert.trial 1993 44),
  (5, PCert.lucas 25943 5 [PCert.trial 2 1, PCert.trial 7 2, PCert.trial 17 4, PCert.trial 109 10]),
  (1, PCert.trial 1997 44)
]
private lemma batch_19_ok : checkBatch 950 batch_19 = true := by decide

private def batch_20 : List (ℕ × PCert) := [
  (1, PCert.trial 1999 44)
]
private lemma batch_20_ok : checkBatch 1000 batch_20 = true := by decide

end OMA.Proof_OeisA232194_conjecture_4_R1_H1

theorem OMA.solution : OMA.R_OeisA232194_conjecture_4_R1.H1 := by
  intro n hn1 hn1000 hn8
  open OMA.Proof_OeisA232194_conjecture_4_R1_H1 in
  if h0 : n < 50 then
    exact checkBatch_spec 0 batch_0 batch_0_ok n (by omega) (by simp [batch_0]; omega) hn1 hn8
  else
  if h1 : n < 100 then
    exact checkBatch_spec 50 batch_1 batch_1_ok n (by omega) (by simp [batch_1]; omega) hn1 hn8
  else
  if h2 : n < 150 then
    exact checkBatch_spec 100 batch_2 batch_2_ok n (by omega) (by simp [batch_2]; omega) hn1 hn8
  else
  if h3 : n < 200 then
    exact checkBatch_spec 150 batch_3 batch_3_ok n (by omega) (by simp [batch_3]; omega) hn1 hn8
  else
  if h4 : n < 250 then
    exact checkBatch_spec 200 batch_4 batch_4_ok n (by omega) (by simp [batch_4]; omega) hn1 hn8
  else
  if h5 : n < 300 then
    exact checkBatch_spec 250 batch_5 batch_5_ok n (by omega) (by simp [batch_5]; omega) hn1 hn8
  else
  if h6 : n < 350 then
    exact checkBatch_spec 300 batch_6 batch_6_ok n (by omega) (by simp [batch_6]; omega) hn1 hn8
  else
  if h7 : n < 400 then
    exact checkBatch_spec 350 batch_7 batch_7_ok n (by omega) (by simp [batch_7]; omega) hn1 hn8
  else
  if h8 : n < 450 then
    exact checkBatch_spec 400 batch_8 batch_8_ok n (by omega) (by simp [batch_8]; omega) hn1 hn8
  else
  if h9 : n < 500 then
    exact checkBatch_spec 450 batch_9 batch_9_ok n (by omega) (by simp [batch_9]; omega) hn1 hn8
  else
  if h10 : n < 550 then
    exact checkBatch_spec 500 batch_10 batch_10_ok n (by omega) (by simp [batch_10]; omega) hn1 hn8
  else
  if h11 : n < 600 then
    exact checkBatch_spec 550 batch_11 batch_11_ok n (by omega) (by simp [batch_11]; omega) hn1 hn8
  else
  if h12 : n < 650 then
    exact checkBatch_spec 600 batch_12 batch_12_ok n (by omega) (by simp [batch_12]; omega) hn1 hn8
  else
  if h13 : n < 700 then
    exact checkBatch_spec 650 batch_13 batch_13_ok n (by omega) (by simp [batch_13]; omega) hn1 hn8
  else
  if h14 : n < 750 then
    exact checkBatch_spec 700 batch_14 batch_14_ok n (by omega) (by simp [batch_14]; omega) hn1 hn8
  else
  if h15 : n < 800 then
    exact checkBatch_spec 750 batch_15 batch_15_ok n (by omega) (by simp [batch_15]; omega) hn1 hn8
  else
  if h16 : n < 850 then
    exact checkBatch_spec 800 batch_16 batch_16_ok n (by omega) (by simp [batch_16]; omega) hn1 hn8
  else
  if h17 : n < 900 then
    exact checkBatch_spec 850 batch_17 batch_17_ok n (by omega) (by simp [batch_17]; omega) hn1 hn8
  else
  if h18 : n < 950 then
    exact checkBatch_spec 900 batch_18 batch_18_ok n (by omega) (by simp [batch_18]; omega) hn1 hn8
  else
  if h19 : n < 1000 then
    exact checkBatch_spec 950 batch_19 batch_19_ok n (by omega) (by simp [batch_19]; omega) hn1 hn8
  else
  exact checkBatch_spec 1000 batch_20 batch_20_ok n (by omega) (by simp [batch_20]; omega) hn1 hn8
