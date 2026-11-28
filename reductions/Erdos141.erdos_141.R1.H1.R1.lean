import OMAReductions.R_Erdos141_erdos_141_R1

-- Reduction Erdos141.erdos_141.R1.H1.R1 of step H1 of Erdos141.erdos_141.R1
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 141, lengths 7 to 10: certificates for lengths 7 and 8

The step asks, for each `7 ≤ k ≤ 10`, for `k` consecutive primes in arithmetic progression.
`main` proves `k = 7` and `k = 8` with explicit progressions of difference `210`, from the
tables of Jens Kruse Andersen and Norman Luhn (The minimal and the smallest known CPAP-k):

* `k = 7`: `71137654873189893604531 + 210 n` (Paul Zimmermann, 2018), 23 digits;
* `k = 8`: `25483976638 · 97# + x36 + 210 n` (Ryan Min June Shin and Sohum Sukhatankar, 2026),
  47 digits, with `x36 = 836699507882418031308586693292191597`.

The certificate lemma `cpap` of the parent reduction asks for primality of the terms and
compositeness of every number between consecutive terms. Both are checked by `decide +kernel`
on Boolean checkers whose soundness is proved here:

* primality: a Lucas (Pratt) certificate for each term and, recursively, for every prime factor
  of `p - 1` (Mathlib `lucas_primality`); the factor lists were computed offline with trial
  division, Pollard rho and ECM, and each entry only uses primes certified before it;
* compositeness: a factor `2, 3, 5` or `7`, or a failed base-`2` Fermat test.

Modular exponentiation is the inline repeated-squaring term `pm_spec` (fuel `1024`), so the file
declares no definition besides the hypotheses.

* `H1`: nine consecutive primes in arithmetic progression (known: the smallest known example has
  48 digits; certificates of the same kind were built for it, ready as a step proof).
* `H2`: ten consecutive primes in arithmetic progression (known: Manfred Toplic, 1998, 93
  digits; full factorizations of `p - 1` were not obtained for every term).
-/

namespace OMA.R_Erdos141_erdos_141_R1_H1_R1

open OMA.R_Erdos141_erdos_141_R1 Erdos141

/-- Nine consecutive primes in arithmetic progression. -/
def H1 : Prop := ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength 9

/-- Ten consecutive primes in arithmetic progression. -/
def H2 : Prop := ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength 10

/-- Repeated squaring with fuel `f` computes `b ^ e % m` when `e < 2 ^ f`. -/
lemma pm_spec : ∀ (f b e m : ℕ), e < 2 ^ f → Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 1 % m) (fun _ ih b e => if e = 0 then 1 % m else (if e % 2 = 1 then b % m else 1) * ih (b * b % m) (e / 2) % m) f b e = b ^ e % m
  | 0, b, e, m, h => by
    have he : e = 0 := by simpa using h
    subst he
    simp
  | f + 1, b, e, m, h => by
    have h2 : e / 2 < 2 ^ f := by
      rw [pow_succ] at h
      omega
    have hstep : Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 1 % m) (fun _ ih b e => if e = 0 then 1 % m else (if e % 2 = 1 then b % m else 1) * ih (b * b % m) (e / 2) % m) (f + 1) b e = (if e = 0 then 1 % m else
        (if e % 2 = 1 then b % m else 1) * Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 1 % m) (fun _ ih b e => if e = 0 then 1 % m else (if e % 2 = 1 then b % m else 1) * ih (b * b % m) (e / 2) % m) f (b * b % m) (e / 2) % m) := rfl
    rw [hstep, pm_spec f (b * b % m) (e / 2) m h2]
    split_ifs with h0 h1
    · subst h0
      simp
    · have he : e = 2 * (e / 2) + 1 := by omega
      have key : b ^ e % m = b % m * ((b * b % m) ^ (e / 2) % m) % m := by
        conv_lhs => rw [he, pow_succ, pow_mul, sq]
        rw [Nat.mul_mod, Nat.pow_mod (b * b), Nat.mul_comm]
      exact key.symm
    · have he : e = 2 * (e / 2) := by omega
      have key : b ^ e % m = 1 * ((b * b % m) ^ (e / 2) % m) % m := by
        conv_lhs => rw [he, pow_mul, sq]
        rw [Nat.pow_mod (b * b), one_mul, Nat.mod_mod]
      exact key.symm

/-- The inline exponentiation used below, at fuel `1024`. -/
lemma pm1024 : ∀ b e m : ℕ, e < 2 ^ 1024 → (fun b e m => Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 1 % m) (fun _ ih b e => if e = 0 then 1 % m else (if e % 2 = 1 then b % m else 1) * ih (b * b % m) (e / 2) % m) 1024 b e) b e m = b ^ e % m :=
  fun b e m h => pm_spec 1024 b e m h

lemma prime_dvd_foldr {q : ℕ} (hq : q.Prime) :
    ∀ fs : List (ℕ × ℕ), (∀ qe ∈ fs, qe.1.Prime) →
      q ∣ fs.foldr (fun qe acc => qe.1 ^ qe.2 * acc) 1 → ∃ qe ∈ fs, qe.1 = q
  | [], _, h => by
    simp only [List.foldr_nil, Nat.dvd_one] at h
    exact absurd h hq.one_lt.ne'
  | qe :: rest, hp, h => by
    simp only [List.foldr_cons] at h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
    · have hr : qe.1.Prime := hp qe (by simp)
      exact ⟨qe, by simp, ((Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow h1)).symm⟩
    · obtain ⟨qe', hmem, heq⟩ := prime_dvd_foldr hq rest (fun x hx => hp x (by simp [hx])) h1
      exact ⟨qe', by simp [hmem], heq⟩

lemma natCast_eq_one {n p : ℕ} [Fact (1 < p)] (h : ((n : ℕ) : ZMod p) = 1) : n % p = 1 := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_one] at hv

/-- Soundness of one Lucas certificate. -/
lemma lucas_sound (pm : ℕ → ℕ → ℕ → ℕ) (hpm : ∀ b e m, e < 2 ^ 1024 → pm b e m = b ^ e % m)
    (c : ℕ × ℕ × List (ℕ × ℕ)) (h : (decide (2 ≤ c.1) && decide (c.1 < 2 ^ 1024) && c.2.2.foldr (fun qe acc => qe.1 ^ qe.2 * acc) 1 == c.1 - 1 && pm c.2.1 (c.1 - 1) c.1 == 1 && c.2.2.all (fun qe => pm c.2.1 ((c.1 - 1) / qe.1) c.1 != 1)) = true) (hfs : ∀ qe ∈ c.2.2, qe.1.Prime) :
    c.1.Prime := by
  obtain ⟨p, a, fs⟩ := c
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, bne_iff_ne,
    ne_eq] at h hfs
  obtain ⟨⟨⟨⟨h2, hbig⟩, hprod⟩, hpow⟩, hall⟩ := h
  have : Fact (1 < p) := ⟨h2⟩
  have hexp : ∀ e, e ≤ p - 1 → pm a e p = a ^ e % p := fun e he => hpm a e p (by omega)
  apply lucas_primality p (a : ZMod p)
  · have h1 : a ^ (p - 1) % p = 1 := by
      rw [← hexp _ le_rfl]
      exact hpow
    have h3 : ((a ^ (p - 1) : ℕ) : ZMod p) = 1 := by
      rw [← ZMod.natCast_mod, h1, Nat.cast_one]
    simpa using h3
  · intro q hq hdvd
    obtain ⟨qe, hmem, rfl⟩ := prime_dvd_foldr hq fs hfs (by rw [hprod]; exact hdvd)
    have hne := hall qe hmem
    rw [hexp _ (Nat.div_le_self _ _)] at hne
    intro hcontra
    apply hne
    apply natCast_eq_one
    simpa using hcontra

lemma fold_false (pm : ℕ → ℕ → ℕ → ℕ) :
    ∀ (cs : List (ℕ × ℕ × List (ℕ × ℕ))) (known : List ℕ),
      (cs.foldl (fun (st : Bool × List ℕ) (c : ℕ × ℕ × List (ℕ × ℕ)) => ((st.1 && (decide (2 ≤ c.1) && decide (c.1 < 2 ^ 1024) && c.2.2.foldr (fun qe acc => qe.1 ^ qe.2 * acc) 1 == c.1 - 1 && pm c.2.1 (c.1 - 1) c.1 == 1 && c.2.2.all (fun qe => pm c.2.1 ((c.1 - 1) / qe.1) c.1 != 1)) && c.2.2.all (fun qe => st.2.contains qe.1)), c.1 :: st.2)) (false, known)).1 = false
  | [], _ => rfl
  | c :: cs, known => by
    simp only [List.foldl_cons, Bool.false_and]
    exact fold_false pm cs (c.1 :: known)

/-- Soundness of a certificate list: each entry is prime when the earlier ones are. -/
lemma certs_sound (pm : ℕ → ℕ → ℕ → ℕ) (hpm : ∀ b e m, e < 2 ^ 1024 → pm b e m = b ^ e % m) :
    ∀ (cs : List (ℕ × ℕ × List (ℕ × ℕ))) (b : Bool) (known : List ℕ),
      (cs.foldl (fun (st : Bool × List ℕ) (c : ℕ × ℕ × List (ℕ × ℕ)) => ((st.1 && (decide (2 ≤ c.1) && decide (c.1 < 2 ^ 1024) && c.2.2.foldr (fun qe acc => qe.1 ^ qe.2 * acc) 1 == c.1 - 1 && pm c.2.1 (c.1 - 1) c.1 == 1 && c.2.2.all (fun qe => pm c.2.1 ((c.1 - 1) / qe.1) c.1 != 1)) && c.2.2.all (fun qe => st.2.contains qe.1)), c.1 :: st.2)) (b, known)).1 = true → (∀ q ∈ known, q.Prime) → ∀ c ∈ cs, c.1.Prime
  | [], _, _, _, _, c, hc => by simp at hc
  | c :: cs, b, known, h, hk, c', hc' => by
    simp only [List.foldl_cons] at h
    cases hb : (b && (decide (2 ≤ c.1) && decide (c.1 < 2 ^ 1024) && c.2.2.foldr (fun qe acc => qe.1 ^ qe.2 * acc) 1 == c.1 - 1 && pm c.2.1 (c.1 - 1) c.1 == 1 && c.2.2.all (fun qe => pm c.2.1 ((c.1 - 1) / qe.1) c.1 != 1)) && c.2.2.all (fun qe => known.contains qe.1)) with
    | false =>
      rw [hb, fold_false pm] at h
      exact absurd h (by decide)
    | true =>
      rw [hb] at h
      have hb1 := (Bool.and_eq_true _ _).mp hb
      have hl := ((Bool.and_eq_true _ _).mp hb1.1).2
      have hf := List.all_eq_true.mp hb1.2
      have hcp : c.1.Prime :=
        lucas_sound pm hpm c hl (fun qe hqe => hk qe.1 (by simpa using hf qe hqe))
      rcases List.mem_cons.mp hc' with rfl | hmem
      · exact hcp
      · refine certs_sound pm hpm cs true (c.1 :: known) h ?_ c' hmem
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hcp
        · exact hk q hq

/-- Soundness of the gap check: a factor `2, 3, 5, 7` or a failed Fermat test. -/
lemma gaps_sound (pm : ℕ → ℕ → ℕ → ℕ) (hpm : ∀ b e m, e < 2 ^ 1024 → pm b e m = b ^ e % m)
    {p N : ℕ} (hp : 7 < p) (hbig : p + N < 2 ^ 1024) (hg : (List.range N).all (fun i => i == 0 || i % 210 == 0 || (p + i) % 2 == 0 || (p + i) % 3 == 0 || (p + i) % 5 == 0 || (p + i) % 7 == 0 || pm 2 (p + i - 1) (p + i) != 1) = true) :
    ∀ i, 0 < i → i < N → i % 210 ≠ 0 → ¬ (p + i).Prime := by
  intro i hi0 hiN h210 hprime
  have h := List.all_eq_true.mp hg i (List.mem_range.mpr hiN)
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  have hdiv : ∀ q, 1 < q → q < p + i → (p + i) % q = 0 → False := fun q h1 h2 h3 => by
    have := Nat.Prime.eq_one_or_self_of_dvd hprime q (Nat.dvd_of_mod_eq_zero h3)
    omega
  rcases h with (((((h | h) | h) | h) | h) | h) | h
  · omega
  · exact h210 h
  · exact hdiv 2 (by norm_num) (by omega) h
  · exact hdiv 3 (by norm_num) (by omega) h
  · exact hdiv 5 (by norm_num) (by omega) h
  · exact hdiv 7 (by norm_num) (by omega) h
  · apply h
    have := Fact.mk hprime
    have : Fact (1 < p + i) := ⟨hprime.one_lt⟩
    have h2 : ((2 : ℕ) : ZMod (p + i)) ≠ 0 := by
      intro h0
      have hv := congrArg ZMod.val h0
      rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
      omega
    have hf := ZMod.pow_card_sub_one_eq_one h2
    rw [hpm 2 (p + i - 1) (p + i) (by omega)]
    apply natCast_eq_one
    rw [Nat.cast_pow]
    exact hf

/-- Certificates give `k` consecutive primes `p + 210 n`. -/
lemma cpap_certs (pm : ℕ → ℕ → ℕ → ℕ) (hpm : ∀ b e m, e < 2 ^ 1024 → pm b e m = b ^ e % m)
    (cs : List (ℕ × ℕ × List (ℕ × ℕ))) (p k : ℕ) (hp : 7 < p)
    (hbig : p + 210 * (k - 1) < 2 ^ 1024) (hc : (cs.foldl (fun (st : Bool × List ℕ) (c : ℕ × ℕ × List (ℕ × ℕ)) => ((st.1 && (decide (2 ≤ c.1) && decide (c.1 < 2 ^ 1024) && c.2.2.foldr (fun qe acc => qe.1 ^ qe.2 * acc) 1 == c.1 - 1 && pm c.2.1 (c.1 - 1) c.1 == 1 && c.2.2.all (fun qe => pm c.2.1 ((c.1 - 1) / qe.1) c.1 != 1)) && c.2.2.all (fun qe => st.2.contains qe.1)), c.1 :: st.2)) (true, [])).1 = true)
    (hterms : (List.range k).all (fun n => (cs.map Prod.fst).contains (p + n * 210)) = true)
    (hg : (List.range (210 * (k - 1))).all (fun i => i == 0 || i % 210 == 0 || (p + i) % 2 == 0 || (p + i) % 3 == 0 || (p + i) % 5 == 0 || (p + i) % 7 == 0 || pm 2 (p + i - 1) (p + i) != 1) = true) :
    ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength k := by
  have hprimes := certs_sound pm hpm cs true [] hc (by simp)
  apply cpap (p := p) (d := 210) (by norm_num)
  · intro n hn
    have hmem := List.all_eq_true.mp hterms n (List.mem_range.mpr hn)
    simp only [List.contains_iff_mem, List.mem_map] at hmem
    obtain ⟨c, hc', hce⟩ := hmem
    rw [← hce]
    exact hprimes c hc'
  · intro n hn m h1 h2
    have hm := gaps_sound pm hpm hp hbig hg (m - p) (by omega) (by omega) (by
      intro h0
      obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h0
      have h3 : n * 210 < 210 * c := by omega
      have h4 : 210 * c < (n + 1) * 210 := by omega
      omega)
    rwa [show p + (m - p) = m by omega] at hm

set_option maxHeartbeats 0 in
/-- Length `7`: 86 Lucas certificates and 1254 gap numbers. -/
lemma case7 : ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength 7 :=
  cpap_certs _ pm1024
    [(2, 1, []),
    (3, 2, [(2, 1)]),
    (5, 2, [(2, 2)]),
    (41, 6, [(2, 3), (5, 1)]),
    (7, 3, [(2, 1), (3, 1)]),
    (43, 3, [(2, 1), (3, 1), (7, 1)]),
    (31, 3, [(2, 1), (3, 1), (5, 1)]),
    (29, 2, [(2, 2), (7, 1)]),
    (59, 2, [(2, 1), (29, 1)]),
    (3187, 2, [(2, 1), (3, 3), (59, 1)]),
    (987971, 6, [(2, 1), (5, 1), (31, 1), (3187, 1)]),
    (19, 2, [(2, 1), (3, 2)]),
    (61, 2, [(2, 2), (3, 1), (5, 1)]),
    (271, 6, [(2, 1), (3, 3), (5, 1)]),
    (6612401, 3, [(2, 4), (5, 2), (61, 1), (271, 1)]),
    (453795855829, 2, [(2, 2), (3, 1), (7, 1), (19, 1), (43, 1), (6612401, 1)]),
    (71137654873189893604531, 2, [(2, 1), (3, 2), (5, 1), (41, 1), (43, 1), (987971, 1), (453795855829, 1)]),
    (281, 3, [(2, 3), (5, 1), (7, 1)]),
    (11, 2, [(2, 1), (5, 1)]),
    (173, 2, [(2, 2), (43, 1)]),
    (190301, 10, [(2, 2), (5, 2), (11, 1), (173, 1)]),
    (89, 3, [(2, 3), (11, 1)]),
    (199, 3, [(2, 1), (3, 2), (11, 1)]),
    (13, 2, [(2, 2), (3, 1)]),
    (1171, 2, [(2, 1), (3, 2), (5, 1), (13, 1)]),
    (932117, 2, [(2, 2), (199, 1), (1171, 1)]),
    (108125573, 2, [(2, 2), (29, 1), (932117, 1)]),
    (38492703989, 2, [(2, 2), (89, 1), (108125573, 1)]),
    (76985407979, 2, [(2, 1), (38492703989, 1)]),
    (703219205942960593, 5, [(2, 4), (3, 1), (190301, 1), (76985407979, 1)]),
    (4219315235657763559, 6, [(2, 1), (3, 1), (703219205942960593, 1)]),
    (71137654873189893604741, 2, [(2, 2), (3, 1), (5, 1), (281, 1), (4219315235657763559, 1)]),
    (37, 2, [(2, 2), (3, 2)]),
    (3257, 3, [(2, 3), (11, 1), (37, 1)]),
    (2281, 7, [(2, 3), (3, 1), (5, 1), (19, 1)]),
    (102301, 7, [(2, 2), (3, 1), (5, 2), (11, 1), (31, 1)]),
    (397, 5, [(2, 2), (3, 2), (11, 1)]),
    (58757, 2, [(2, 2), (37, 1), (397, 1)]),
    (352543, 3, [(2, 1), (3, 1), (58757, 1)]),
    (2467962263744491, 2, [(2, 1), (3, 1), (5, 1), (2281, 1), (102301, 1), (352543, 1)]),
    (71137654873189893604951, 3, [(2, 1), (3, 1), (5, 2), (59, 1), (3257, 1), (2467962263744491, 1)]),
    (2243, 2, [(2, 1), (19, 1), (59, 1)]),
    (23, 5, [(2, 1), (11, 1)]),
    (1289, 6, [(2, 3), (7, 1), (23, 1)]),
    (2579, 2, [(2, 1), (1289, 1)]),
    (7321, 7, [(2, 3), (3, 1), (5, 1), (61, 1)]),
    (17, 3, [(2, 4)]),
    (71, 7, [(2, 1), (5, 1), (7, 1)]),
    (33797, 3, [(2, 2), (7, 1), (17, 1), (71, 1)]),
    (145982423831, 17, [(2, 1), (5, 1), (59, 1), (7321, 1), (33797, 1)]),
    (88098349028074867, 2, [(2, 1), (3, 2), (13, 1), (2579, 1), (145982423831, 1)]),
    (71137654873189893605161, 7, [(2, 3), (3, 2), (5, 1), (2243, 1), (88098349028074867, 1)]),
    (1567, 3, [(2, 1), (3, 3), (29, 1)]),
    (6269, 2, [(2, 2), (1567, 1)]),
    (1404257, 3, [(2, 5), (7, 1), (6269, 1)]),
    (8933, 2, [(2, 2), (7, 1), (11, 1), (29, 1)]),
    (4341439, 3, [(2, 1), (3, 5), (8933, 1)]),
    (67, 2, [(2, 1), (3, 1), (11, 1)]),
    (2791, 6, [(2, 1), (3, 2), (5, 1), (31, 1)]),
    (29919521, 3, [(2, 5), (5, 1), (67, 1), (2791, 1)]),
    (71137654873189893605371, 26, [(2, 1), (3, 1), (5, 1), (13, 1), (1404257, 1), (4341439, 1), (29919521, 1)]),
    (83, 2, [(2, 1), (41, 1)]),
    (9463, 3, [(2, 1), (3, 1), (19, 1), (83, 1)]),
    (37853, 2, [(2, 2), (9463, 1)]),
    (75707, 2, [(2, 1), (37853, 1)]),
    (109, 6, [(2, 2), (3, 3)]),
    (73, 5, [(2, 3), (3, 2)]),
    (12119, 7, [(2, 1), (73, 1), (83, 1)]),
    (24239, 13, [(2, 1), (12119, 1)]),
    (48479, 7, [(2, 1), (24239, 1)]),
    (97, 5, [(2, 5), (3, 1)]),
    (1553, 3, [(2, 4), (97, 1)]),
    (1257931, 2, [(2, 1), (3, 4), (5, 1), (1553, 1)]),
    (121966473899, 2, [(2, 1), (48479, 1), (1257931, 1)]),
    (15660739181579399, 13, [(2, 1), (19, 1), (31, 1), (109, 1), (121966473899, 1)]),
    (71137654873189893605581, 2, [(2, 2), (3, 1), (5, 1), (75707, 1), (15660739181579399, 1)]),
    (373, 2, [(2, 2), (3, 1), (31, 1)]),
    (1051, 7, [(2, 1), (3, 1), (5, 2), (7, 1)]),
    (2352139, 2, [(2, 1), (3, 1), (373, 1), (1051, 1)]),
    (439, 15, [(2, 1), (3, 1), (73, 1)]),
    (701, 2, [(2, 2), (5, 2), (7, 1)]),
    (523, 2, [(2, 1), (3, 2), (29, 1)]),
    (6277, 2, [(2, 2), (3, 1), (523, 1)]),
    (127578731939, 2, [(2, 1), (7, 1), (19, 1), (109, 1), (701, 1), (6277, 1)]),
    (112014126642443, 2, [(2, 1), (439, 1), (127578731939, 1)]),
    (71137654873189893605791, 3, [(2, 1), (3, 3), (5, 1), (2352139, 1), (112014126642443, 1)])]
    71137654873189893604531 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

set_option maxHeartbeats 0 in
/-- Length `8`: 173 Lucas certificates and 1463 gap numbers. -/
lemma case8 : ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength 8 :=
  cpap_certs _ pm1024
    [(2, 1, []),
    (3, 2, [(2, 1)]),
    (7, 3, [(2, 1), (3, 1)]),
    (17, 3, [(2, 4)]),
    (19, 2, [(2, 1), (3, 2)]),
    (5, 2, [(2, 2)]),
    (41, 6, [(2, 3), (5, 1)]),
    (83, 2, [(2, 1), (41, 1)]),
    (73, 5, [(2, 3), (3, 2)]),
    (877, 2, [(2, 2), (3, 1), (73, 1)]),
    (13, 2, [(2, 2), (3, 1)]),
    (6761, 3, [(2, 3), (5, 1), (13, 2)]),
    (439, 15, [(2, 1), (3, 1), (73, 1)]),
    (958777, 5, [(2, 3), (3, 1), (7, 1), (13, 1), (439, 1)]),
    (11, 2, [(2, 1), (5, 1)]),
    (23, 5, [(2, 1), (11, 1)]),
    (47, 5, [(2, 1), (23, 1)]),
    (79, 3, [(2, 1), (3, 1), (13, 1)]),
    (3793, 5, [(2, 4), (3, 1), (79, 1)]),
    (103, 5, [(2, 1), (3, 1), (17, 1)]),
    (7211, 2, [(2, 1), (5, 1), (7, 1), (103, 1)]),
    (15426146173, 19, [(2, 2), (3, 1), (47, 1), (3793, 1), (7211, 1)]),
    (37, 2, [(2, 2), (3, 2)]),
    (137, 3, [(2, 3), (17, 1)]),
    (761, 6, [(2, 3), (5, 1), (19, 1)]),
    (1523, 2, [(2, 1), (761, 1)]),
    (496589381, 10, [(2, 2), (5, 1), (7, 1), (17, 1), (137, 1), (1523, 1)]),
    (2855388940751, 7, [(2, 1), (5, 3), (23, 1), (496589381, 1)]),
    (4648573195542629, 2, [(2, 2), (11, 1), (37, 1), (2855388940751, 1)]),
    (5143123260797051588680762786409199266166569, 3, [(2, 3), (19, 1), (83, 1), (877, 1), (6761, 1), (958777, 1), (15426146173, 1), (4648573195542629, 1)]),
    (58755040131345517349089034071938692416686884257, 5, [(2, 5), (3, 1), (7, 1), (17, 1), (5143123260797051588680762786409199266166569, 1)]),
    (491, 2, [(2, 1), (5, 1), (7, 2)]),
    (983, 5, [(2, 1), (491, 1)]),
    (131, 2, [(2, 1), (5, 1), (13, 1)]),
    (263, 5, [(2, 1), (131, 1)]),
    (5261, 2, [(2, 2), (5, 1), (263, 1)]),
    (42089, 3, [(2, 3), (5261, 1)]),
    (96769, 22, [(2, 9), (3, 3), (7, 1)]),
    (387077, 2, [(2, 2), (96769, 1)]),
    (192176702729989, 2, [(2, 2), (3, 1), (983, 1), (42089, 1), (387077, 1)]),
    (421, 2, [(2, 2), (3, 1), (5, 1), (7, 1)]),
    (29, 2, [(2, 2), (7, 1)]),
    (233, 3, [(2, 3), (29, 1)]),
    (7457, 3, [(2, 5), (233, 1)]),
    (89, 3, [(2, 3), (11, 1)]),
    (179, 2, [(2, 1), (89, 1)]),
    (1129, 11, [(2, 3), (3, 1), (47, 1)]),
    (7841, 12, [(2, 5), (5, 1), (7, 2)]),
    (15683, 2, [(2, 1), (7841, 1)]),
    (76065435673, 5, [(2, 3), (3, 1), (179, 1), (1129, 1), (15683, 1)]),
    (53, 2, [(2, 2), (13, 1)]),
    (139, 2, [(2, 1), (3, 1), (23, 1)]),
    (31, 3, [(2, 1), (3, 1), (5, 1)]),
    (2543, 5, [(2, 1), (31, 1), (41, 1)]),
    (157667, 2, [(2, 1), (31, 1), (2543, 1)]),
    (1693514806363, 2, [(2, 1), (3, 6), (53, 1), (139, 1), (157667, 1)]),
    (2426463955765949267364502312219, 2, [(2, 1), (3, 1), (421, 1), (7457, 1), (76065435673, 1), (1693514806363, 1)]),
    (58755040131345517349089034071938692416686884467, 2, [(2, 1), (3, 2), (7, 1), (192176702729989, 1), (2426463955765949267364502312219, 1)]),
    (251, 6, [(2, 1), (5, 3)]),
    (1051, 7, [(2, 1), (3, 1), (5, 2), (7, 1)]),
    (12613, 2, [(2, 2), (3, 1), (1051, 1)]),
    (277, 5, [(2, 2), (3, 1), (23, 1)]),
    (52631, 13, [(2, 1), (5, 1), (19, 1), (277, 1)]),
    (71, 7, [(2, 1), (5, 1), (7, 1)]),
    (569, 3, [(2, 3), (71, 1)]),
    (1295947, 2, [(2, 1), (3, 3), (103, 1), (233, 1)]),
    (1474787687, 5, [(2, 1), (569, 1), (1295947, 1)]),
    (5874092361998823967, 7, [(2, 1), (3, 1), (12613, 1), (52631, 1), (1474787687, 1)]),
    (2741, 2, [(2, 2), (5, 1), (137, 1)]),
    (6217, 5, [(2, 3), (3, 1), (7, 1), (37, 1)]),
    (62171, 2, [(2, 1), (5, 1), (6217, 1)]),
    (281, 3, [(2, 3), (5, 1), (7, 1)]),
    (563, 2, [(2, 1), (281, 1)]),
    (23139271, 7, [(2, 1), (3, 4), (5, 1), (7, 2), (11, 1), (53, 1)]),
    (182383734023, 5, [(2, 1), (7, 1), (563, 1), (23139271, 1)]),
    (1118885104428995532709, 2, [(2, 2), (3, 2), (2741, 1), (62171, 1), (182383734023, 1)]),
    (474407284277894105868617, 3, [(2, 3), (53, 1), (1118885104428995532709, 1)]),
    (58755040131345517349089034071938692416686884677, 5, [(2, 2), (3, 1), (7, 1), (251, 1), (5874092361998823967, 1), (474407284277894105868617, 1)]),
    (20521, 11, [(2, 3), (3, 3), (5, 1), (19, 1)]),
    (43, 3, [(2, 1), (3, 1), (7, 1)]),
    (173, 2, [(2, 2), (43, 1)]),
    (347, 2, [(2, 1), (173, 1)]),
    (757, 2, [(2, 2), (3, 3), (7, 1)]),
    (40879, 6, [(2, 1), (3, 3), (757, 1)]),
    (1049, 3, [(2, 3), (131, 1)]),
    (2099, 2, [(2, 1), (1049, 1)]),
    (2593, 7, [(2, 5), (3, 4)]),
    (43541657, 3, [(2, 3), (2099, 1), (2593, 1)]),
    (429876723528232537, 5, [(2, 3), (3, 1), (29, 1), (347, 1), (40879, 1), (43541657, 1)]),
    (7019, 2, [(2, 1), (11, 2), (29, 1)]),
    (151, 6, [(2, 1), (3, 1), (5, 2)]),
    (3221, 10, [(2, 2), (5, 1), (7, 1), (23, 1)]),
    (109, 6, [(2, 2), (3, 3)]),
    (1091, 2, [(2, 1), (5, 1), (109, 1)]),
    (150559, 3, [(2, 1), (3, 1), (23, 1), (1091, 1)]),
    (66051233312879, 11, [(2, 1), (11, 1), (41, 1), (151, 1), (3221, 1), (150559, 1)]),
    (6894861557698709009273, 3, [(2, 3), (11, 1), (13, 2), (7019, 1), (66051233312879, 1)]),
    (58755040131345517349089034071938692416686884887, 6, [(2, 1), (3, 1), (7, 1), (23, 1), (20521, 1), (429876723528232537, 1), (6894861557698709009273, 1)]),
    (547601, 3, [(2, 4), (5, 2), (37, 2)]),
    (271, 6, [(2, 1), (3, 3), (5, 1)]),
    (659, 2, [(2, 1), (7, 1), (47, 1)]),
    (61, 2, [(2, 2), (3, 1), (5, 1)]),
    (733, 6, [(2, 2), (3, 1), (61, 1)]),
    (7331, 2, [(2, 1), (5, 1), (733, 1)]),
    (317, 2, [(2, 2), (79, 1)]),
    (28621, 13, [(2, 2), (3, 3), (5, 1), (53, 1)]),
    (163311427, 2, [(2, 1), (3, 2), (317, 1), (28621, 1)]),
    (1633114271, 17, [(2, 1), (5, 1), (163311427, 1)]),
    (167, 5, [(2, 1), (83, 1)]),
    (911, 17, [(2, 1), (5, 1), (7, 1), (13, 1)]),
    (2324873, 3, [(2, 3), (11, 1), (29, 1), (911, 1)]),
    (18831471301, 2, [(2, 2), (3, 4), (5, 2), (2324873, 1)]),
    (39795004119756619, 3, [(2, 1), (3, 2), (19, 1), (37, 1), (167, 1), (18831471301, 1)]),
    (510521813478962404726800818290585747, 2, [(2, 1), (3, 1), (271, 1), (659, 1), (7331, 1), (1633114271, 1), (39795004119756619, 1)]),
    (58755040131345517349089034071938692416686885097, 5, [(2, 3), (3, 3), (7, 1), (139, 1), (547601, 1), (510521813478962404726800818290585747, 1)]),
    (337, 10, [(2, 4), (3, 1), (7, 1)]),
    (6067, 2, [(2, 1), (3, 2), (337, 1)]),
    (373, 2, [(2, 2), (3, 1), (31, 1)]),
    (977, 3, [(2, 4), (61, 1)]),
    (2915369, 3, [(2, 3), (373, 1), (977, 1)]),
    (547, 2, [(2, 1), (3, 1), (7, 1), (13, 1)]),
    (33066151, 3, [(2, 1), (3, 1), (5, 2), (13, 1), (31, 1), (547, 1)]),
    (10025603283770777, 3, [(2, 3), (13, 1), (2915369, 1), (33066151, 1)]),
    (67, 2, [(2, 1), (3, 1), (11, 1)]),
    (449, 3, [(2, 6), (7, 1)]),
    (80742773, 2, [(2, 2), (11, 1), (61, 1), (67, 1), (449, 1)]),
    (4521595289, 3, [(2, 3), (7, 1), (80742773, 1)]),
    (1061, 2, [(2, 2), (5, 1), (53, 1)]),
    (293, 2, [(2, 2), (73, 1)]),
    (397, 5, [(2, 2), (3, 2), (11, 1)]),
    (232643, 2, [(2, 1), (293, 1), (397, 1)]),
    (65211627042817, 5, [(2, 11), (3, 1), (43, 1), (1061, 1), (232643, 1)]),
    (1769163513748958090934679, 3, [(2, 1), (3, 1), (4521595289, 1), (65211627042817, 1)]),
    (58755040131345517349089034071938692416686885307, 2, [(2, 1), (3, 1), (7, 1), (13, 1), (6067, 1), (10025603283770777, 1), (1769163513748958090934679, 1)]),
    (229, 6, [(2, 2), (3, 1), (19, 1)]),
    (101, 2, [(2, 2), (5, 2)]),
    (607, 3, [(2, 1), (3, 1), (101, 1)]),
    (3643, 2, [(2, 1), (3, 1), (607, 1)]),
    (127, 3, [(2, 1), (3, 2), (7, 1)]),
    (1489, 14, [(2, 4), (3, 1), (31, 1)]),
    (580711, 3, [(2, 1), (3, 1), (5, 1), (13, 1), (1489, 1)]),
    (25517602763, 2, [(2, 1), (127, 1), (173, 1), (580711, 1)]),
    (215164426497617, 3, [(2, 4), (17, 1), (31, 1), (25517602763, 1)]),
    (14109192103154737159, 3, [(2, 1), (3, 2), (3643, 1), (215164426497617, 1)]),
    (509, 2, [(2, 2), (127, 1)]),
    (1031, 14, [(2, 1), (5, 1), (103, 1)]),
    (2063, 5, [(2, 1), (1031, 1)]),
    (97, 5, [(2, 5), (3, 1)]),
    (48889, 34, [(2, 3), (3, 2), (7, 1), (97, 1)]),
    (227920519, 3, [(2, 1), (3, 2), (7, 1), (37, 1), (48889, 1)]),
    (29629667471, 23, [(2, 1), (5, 1), (13, 1), (227920519, 1)]),
    (210370639044101, 3, [(2, 2), (5, 2), (71, 1), (29629667471, 1)]),
    (4418065316582440095341, 3, [(2, 2), (5, 1), (509, 1), (2063, 1), (210370639044101, 1)]),
    (58755040131345517349089034071938692416686885517, 2, [(2, 2), (3, 1), (7, 3), (229, 1), (14109192103154737159, 1), (4418065316582440095341, 1)]),
    (2857, 11, [(2, 3), (3, 1), (7, 1), (17, 1)]),
    (28571, 2, [(2, 1), (5, 1), (2857, 1)]),
    (57143, 5, [(2, 1), (28571, 1)]),
    (149, 2, [(2, 2), (37, 1)]),
    (61091, 2, [(2, 1), (5, 1), (41, 1), (149, 1)]),
    (59, 2, [(2, 1), (29, 1)]),
    (11447, 5, [(2, 1), (59, 1), (97, 1)]),
    (110578021, 2, [(2, 2), (3, 1), (5, 1), (7, 1), (23, 1), (11447, 1)]),
    (114116517673, 5, [(2, 3), (3, 1), (43, 1), (110578021, 1)]),
    (457, 13, [(2, 3), (3, 1), (19, 1)]),
    (571, 3, [(2, 1), (3, 1), (5, 1), (19, 1)]),
    (31313641, 13, [(2, 3), (3, 1), (5, 1), (457, 1), (571, 1)]),
    (1759, 6, [(2, 1), (3, 1), (293, 1)]),
    (1483, 2, [(2, 1), (3, 1), (13, 1), (19, 1)]),
    (4244347, 2, [(2, 1), (3, 3), (53, 1), (1483, 1)]),
    (1502498839, 7, [(2, 1), (3, 1), (59, 1), (4244347, 1)]),
    (42286327324817, 3, [(2, 4), (1759, 1), (1502498839, 1)]),
    (1170538763783103976968149, 2, [(2, 2), (13, 1), (17, 1), (31313641, 1), (42286327324817, 1)]),
    (58755040131345517349089034071938692416686885727, 5, [(2, 1), (3, 2), (7, 1), (57143, 1), (61091, 1), (114116517673, 1), (1170538763783103976968149, 1)])]
    58755040131345517349089034071938692416686884257 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem main : H1 → H2 → OMA.R_Erdos141_erdos_141_R1.H1 := by
  intro h1 h2
  unfold OMA.R_Erdos141_erdos_141_R1.H1
  intro k hk1 hk2
  rcases (show k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 by omega) with h | h | h | h
  · subst h
    exact case7
  · subst h
    exact case8
  · subst h
    exact h1
  · subst h
    exact h2

end OMA.R_Erdos141_erdos_141_R1_H1_R1
