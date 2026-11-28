import OMAReductions.R_OeisA7918_conjecture1_R2
import Mathlib

/-!
# Proof of `OeisA7918.conjecture1.R2.H1`

We prove that for every `1 <= n <= 20`, there exists a positive common difference `d` such that
`OeisA7918.isApOfNPrimes n (OeisA7918.a n) d` holds (an arithmetic progression of `n` primes
starting at `a n`, the least prime `>= n`).

For `n <= 19` we use the minimal common differences from OEIS A061558 (Gusev, Carmody,
Izykowski), and for `n = 20` we use Wojciech Izykowski's 2017 AP-20 starting at `23` with
common difference `134181089232118748020 * 19#`. Every prime term `> 1000` is verified in the
Lean kernel by Pratt/Lucas primality certificates using structurally recursive binary modular
exponentiation (`powModFuel`), and primes `<= 1000` are verified by trial division up to `32`.
-/

namespace OeisA7918R2H1

private def powModFuel : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | fuel + 1, a, e, m =>
    if e = 0 then 1 % m
    else
      let h := powModFuel fuel a (e / 2) m
      let sq := (h * h) % m
      if e % 2 = 0 then sq else (sq * a) % m

private lemma powModFuel_eq : ∀ (fuel a e m : ℕ), e < 2 ^ fuel →
    powModFuel fuel a e m = a ^ e % m
  | 0, a, e, m, h => by
    have he0 : e = 0 := by omega
    subst he0
    simp [powModFuel]
  | fuel + 1, a, e, m, h => by
    unfold powModFuel
    split_ifs with he0 heven
    · subst he0
      simp
    · have hhalf : e / 2 < 2 ^ fuel := by
        have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        omega
      rw [powModFuel_eq fuel a (e / 2) m hhalf]
      have hsq : (a ^ (e / 2) % m * (a ^ (e / 2) % m)) % m = a ^ (e / 2 + e / 2) % m := by
        rw [← Nat.mul_mod, ← pow_add]
      have heq : e / 2 + e / 2 = e := by omega
      dsimp only
      rw [hsq, heq]
    · have hhalf : e / 2 < 2 ^ fuel := by
        have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        omega
      rw [powModFuel_eq fuel a (e / 2) m hhalf]
      have hsq : (a ^ (e / 2) % m * (a ^ (e / 2) % m)) % m = a ^ (e / 2 + e / 2) % m := by
        rw [← Nat.mul_mod, ← pow_add]
      have hstep : (a ^ (e / 2 + e / 2) % m * a) % m = a ^ (e / 2 + e / 2 + 1) % m := by
        rw [Nat.mod_mul_mod, pow_succ]
      have heq : e / 2 + e / 2 + 1 = e := by omega
      dsimp only
      rw [hsq, hstep, heq]

private def hasNoDivisorUpTo (n : ℕ) : ℕ → Bool
  | 0 => true
  | 1 => true
  | d + 2 => (n % (d + 2) != 0) && hasNoDivisorUpTo n (d + 1)

private lemma hasNoDivisorUpTo_spec {n k : ℕ} (h : hasNoDivisorUpTo n k = true) :
    ∀ d : ℕ, 2 ≤ d → d ≤ k → ¬ (d ∣ n) := by
  induction k with
  | zero => intro d hd1 hd2; omega
  | succ k ih =>
    cases k with
    | zero => intro d hd1 hd2; omega
    | succ m =>
      simp only [hasNoDivisorUpTo, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      intro d hd1 hd2 hdvd
      by_cases hdm : d = m + 2
      · subst hdm
        exact h.1 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact ih h.2 d hd1 (by omega) hdvd

private def isPrimeSmall (n : ℕ) : Bool :=
  decide (2 ≤ n) && decide (n ≤ 1000) && hasNoDivisorUpTo n (min 32 (n - 1))

private lemma prime_of_isPrimeSmall {n : ℕ} (h : isPrimeSmall n = true) : n.Prime := by
  simp only [isPrimeSmall, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hn2, hn1000⟩, hnd⟩ := h
  by_contra hnp
  have hmf_prime : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hmf_sq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  have hmf_le32 : n.minFac ≤ 32 := by nlinarith
  have hmf_lt : n.minFac < n := by
    have hle : n.minFac ≤ n := Nat.le_of_dvd (by omega) (Nat.minFac_dvd n)
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso; rw [heq] at hmf_prime; exact hnp hmf_prime
  exact hasNoDivisorUpTo_spec hnd n.minFac hmf_prime.two_le (by omega) (Nat.minFac_dvd n)

private def prodPow : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (q, e) :: rest => q ^ e * prodPow rest

private lemma dvd_prodPow_mem {q : ℕ} (hq : q.Prime) :
    ∀ {fs : List (ℕ × ℕ)}, (∀ qe ∈ fs, qe.1.Prime) → q ∣ prodPow fs →
      ∃ e : ℕ, (q, e) ∈ fs
  | [], _, hdvd => by
    simp only [prodPow] at hdvd
    exact (hq.ne_one (Nat.eq_one_of_dvd_one hdvd)).elim
  | (q₁, e₁) :: rest, hpr, hdvd => by
    simp only [prodPow] at hdvd
    rcases hq.dvd_mul.mp hdvd with hleft | hright
    · have hqq₁ : q ∣ q₁ := hq.dvd_of_dvd_pow hleft
      have hq₁p : q₁.Prime := hpr (q₁, e₁) (List.mem_cons_self ..)
      rcases (Nat.dvd_prime hq₁p).mp hqq₁ with h1 | heq
      · exact (hq.ne_one h1).elim
      · subst heq
        exact ⟨e₁, List.mem_cons_self ..⟩
    · obtain ⟨e, he⟩ := dvd_prodPow_mem hq (fun qe hqe => hpr qe (List.mem_cons_of_mem _ hqe)) hright
      exact ⟨e, List.mem_cons_of_mem _ he⟩

private def lucasCheck (p a : ℕ) (fs : List (ℕ × ℕ)) : Bool :=
  decide (2 ≤ p) &&
  decide (p < 2 ^ 100) &&
  decide (prodPow fs = p - 1) &&
  decide (powModFuel 100 a (p - 1) p = 1) &&
  fs.all (fun qe => decide (powModFuel 100 a ((p - 1) / qe.1) p != 1))

private lemma prime_of_totient_ge {p : ℕ} (hp2 : 2 ≤ p) (htot : p - 1 ≤ p.totient) : p.Prime := by
  by_contra hnp
  have hmf_prime : p.minFac.Prime := Nat.minFac_prime (by omega)
  have hmf_dvd : p.minFac ∣ p := Nat.minFac_dvd p
  have hmf_lt : p.minFac < p := by
    have hle : p.minFac ≤ p := Nat.le_of_dvd (by omega) hmf_dvd
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso; rw [heq] at hmf_prime; exact hnp hmf_prime
  have hmf_pos : 0 < p.minFac := hmf_prime.pos
  have hnotcop0 : ¬ p.Coprime 0 := by
    intro hc
    have := (Nat.coprime_zero_right p).mp hc
    omega
  have hnotcopd : ¬ p.Coprime p.minFac := by
    intro hc
    have h1 : p.minFac ∣ Nat.gcd p p.minFac := Nat.dvd_gcd hmf_dvd dvd_rfl
    rw [hc.gcd_eq_one] at h1
    exact hmf_prime.ne_one (Nat.eq_one_of_dvd_one h1)
  have hsub : (Finset.range p).filter p.Coprime ⊆ ((Finset.range p).erase 0).erase p.minFac := by
    intro x hx
    rw [Finset.mem_filter] at hx
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, hx.1⟩
    · rintro rfl; exact hnotcopd hx.2
    · rintro rfl; exact hnotcop0 hx.2
  have hcard1 : ((Finset.range p).filter p.Coprime).card = p.totient := by
    rw [Nat.totient_eq_card_coprime]
  have hmem0 : (0 : ℕ) ∈ Finset.range p := Finset.mem_range.mpr (by omega)
  have hmemd : p.minFac ∈ (Finset.range p).erase 0 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr hmf_lt⟩
  have hcard2 : (((Finset.range p).erase 0).erase p.minFac).card = p - 2 := by
    rw [Finset.card_erase_of_mem hmemd, Finset.card_erase_of_mem hmem0, Finset.card_range]
    omega
  have hle : p.totient ≤ p - 2 := by
    rw [← hcard1, ← hcard2]
    exact Finset.card_le_card hsub
  omega

private lemma prime_of_lucasCheck {p a : ℕ} {fs : List (ℕ × ℕ)}
    (hcheck : lucasCheck p a fs = true) (hprimes : ∀ qe ∈ fs, qe.1.Prime) : p.Prime := by
  simp only [lucasCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne,
    ne_eq] at hcheck
  obtain ⟨⟨⟨⟨hp2, hplt⟩, hprod⟩, hpow1⟩, hsub⟩ := hcheck
  rw [powModFuel_eq 100 a (p - 1) p (by omega)] at hpow1
  have : NeZero p := ⟨by omega⟩
  let x : ZMod p := (a : ZMod p)
  have hmod1 : ∀ k : ℕ, x ^ k = 1 ↔ a ^ k % p = 1 := by
    intro k
    have hcast : x ^ k = ((a ^ k : ℕ) : ZMod p) := by simp [x]
    rw [hcast, show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by simp, ZMod.natCast_eq_natCast_iff]
    change a ^ k % p = 1 % p ↔ a ^ k % p = 1
    rw [Nat.mod_eq_of_lt (by omega : 1 < p)]
  have hxpow : x ^ (p - 1) = 1 := (hmod1 (p - 1)).mpr hpow1
  have hdvd : orderOf x ∣ p - 1 := orderOf_dvd_of_pow_eq_one hxpow
  have hord_pos : 0 < orderOf x := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hord_eq : orderOf x = p - 1 := by
    by_contra hne
    have hlt : orderOf x < p - 1 := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd) hne
    let r : ℕ := (p - 1) / orderOf x
    have hmul : orderOf x * r = p - 1 := Nat.mul_div_cancel' hdvd
    have hr2 : 2 ≤ r := by nlinarith
    let q : ℕ := r.minFac
    have hq_prime : q.Prime := Nat.minFac_prime (by omega)
    have hq_dvd_r : q ∣ r := Nat.minFac_dvd r
    have hq_dvd_pm1 : q ∣ prodPow fs := by
      rw [hprod, ← hmul]
      exact dvd_mul_of_dvd_right hq_dvd_r _
    obtain ⟨e, hqe_mem⟩ := dvd_prodPow_mem hq_prime hprimes hq_dvd_pm1
    obtain ⟨m, hm⟩ := hq_dvd_r
    have hdiv_eq : (p - 1) / q = orderOf x * m := by
      have h1 : p - 1 = (orderOf x * m) * q := by
        rw [← hmul, hm]; ring
      rw [h1, Nat.mul_div_cancel _ hq_prime.pos]
    have hxsub : x ^ ((p - 1) / q) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp ⟨m, hdiv_eq⟩
    have hbad := hsub (q, e) hqe_mem
    have hdiv_lt : (p - 1) / q < 2 ^ 100 :=
      lt_of_le_of_lt (Nat.div_le_self (p - 1) q) (by omega)
    rw [powModFuel_eq 100 a ((p - 1) / q) p hdiv_lt] at hbad
    exact hbad ((hmod1 ((p - 1) / q)).mp hxsub)
  have hmul1 : x * x ^ (p - 2) = 1 := by
    rw [← pow_succ', show p - 2 + 1 = p - 1 by omega, hxpow]
  let u : (ZMod p)ˣ := Units.mkOfMulEqOne x (x ^ (p - 2)) hmul1
  have hu_val : (u : ZMod p) = x := rfl
  have hu_ord : orderOf u = p - 1 := by
    rw [← orderOf_units, hu_val, hord_eq]
  have hlag : p - 1 ∣ p.totient := by
    rw [← hu_ord, ← ZMod.card_units_eq_totient p]
    exact orderOf_dvd_card
  have htot_pos : 0 < p.totient := Nat.totient_pos.mpr (by omega)
  exact prime_of_totient_ge hp2 (Nat.le_of_dvd htot_pos hlag)

private lemma all_primes_nil : ∀ qe ∈ ([] : List (ℕ × ℕ)), qe.1.Prime := by
  intro _ h; simp at h

private lemma all_primes_cons {q e : ℕ} {rest : List (ℕ × ℕ)} (hq : q.Prime)
    (hrest : ∀ qe ∈ rest, qe.1.Prime) : ∀ qe ∈ (q, e) :: rest, qe.1.Prime := by
  intro qe hqe
  rcases List.mem_cons.mp hqe with rfl | htail
  · exact hq
  · exact hrest qe htail

private lemma sp_2 : Nat.Prime 2 := prime_of_isPrimeSmall (by decide)

private lemma sp_3 : Nat.Prime 3 := prime_of_isPrimeSmall (by decide)

private lemma sp_5 : Nat.Prime 5 := prime_of_isPrimeSmall (by decide)

private lemma sp_7 : Nat.Prime 7 := prime_of_isPrimeSmall (by decide)

private lemma sp_11 : Nat.Prime 11 := prime_of_isPrimeSmall (by decide)

private lemma sp_13 : Nat.Prime 13 := prime_of_isPrimeSmall (by decide)

private lemma sp_17 : Nat.Prime 17 := prime_of_isPrimeSmall (by decide)

private lemma sp_19 : Nat.Prime 19 := prime_of_isPrimeSmall (by decide)

private lemma sp_23 : Nat.Prime 23 := prime_of_isPrimeSmall (by decide)

private lemma sp_29 : Nat.Prime 29 := prime_of_isPrimeSmall (by decide)

private lemma sp_31 : Nat.Prime 31 := prime_of_isPrimeSmall (by decide)

private lemma sp_37 : Nat.Prime 37 := prime_of_isPrimeSmall (by decide)

private lemma sp_41 : Nat.Prime 41 := prime_of_isPrimeSmall (by decide)

private lemma sp_43 : Nat.Prime 43 := prime_of_isPrimeSmall (by decide)

private lemma sp_47 : Nat.Prime 47 := prime_of_isPrimeSmall (by decide)

private lemma sp_53 : Nat.Prime 53 := prime_of_isPrimeSmall (by decide)

private lemma sp_59 : Nat.Prime 59 := prime_of_isPrimeSmall (by decide)

private lemma sp_61 : Nat.Prime 61 := prime_of_isPrimeSmall (by decide)

private lemma sp_67 : Nat.Prime 67 := prime_of_isPrimeSmall (by decide)

private lemma sp_71 : Nat.Prime 71 := prime_of_isPrimeSmall (by decide)

private lemma sp_73 : Nat.Prime 73 := prime_of_isPrimeSmall (by decide)

private lemma sp_79 : Nat.Prime 79 := prime_of_isPrimeSmall (by decide)

private lemma sp_83 : Nat.Prime 83 := prime_of_isPrimeSmall (by decide)

private lemma sp_89 : Nat.Prime 89 := prime_of_isPrimeSmall (by decide)

private lemma sp_97 : Nat.Prime 97 := prime_of_isPrimeSmall (by decide)

private lemma sp_101 : Nat.Prime 101 := prime_of_isPrimeSmall (by decide)

private lemma sp_103 : Nat.Prime 103 := prime_of_isPrimeSmall (by decide)

private lemma sp_107 : Nat.Prime 107 := prime_of_isPrimeSmall (by decide)

private lemma sp_109 : Nat.Prime 109 := prime_of_isPrimeSmall (by decide)

private lemma sp_113 : Nat.Prime 113 := prime_of_isPrimeSmall (by decide)

private lemma sp_127 : Nat.Prime 127 := prime_of_isPrimeSmall (by decide)

private lemma sp_131 : Nat.Prime 131 := prime_of_isPrimeSmall (by decide)

private lemma sp_137 : Nat.Prime 137 := prime_of_isPrimeSmall (by decide)

private lemma sp_139 : Nat.Prime 139 := prime_of_isPrimeSmall (by decide)

private lemma sp_151 : Nat.Prime 151 := prime_of_isPrimeSmall (by decide)

private lemma sp_157 : Nat.Prime 157 := prime_of_isPrimeSmall (by decide)

private lemma sp_163 : Nat.Prime 163 := prime_of_isPrimeSmall (by decide)

private lemma sp_173 : Nat.Prime 173 := prime_of_isPrimeSmall (by decide)

private lemma sp_179 : Nat.Prime 179 := prime_of_isPrimeSmall (by decide)

private lemma sp_181 : Nat.Prime 181 := prime_of_isPrimeSmall (by decide)

private lemma sp_191 : Nat.Prime 191 := prime_of_isPrimeSmall (by decide)

private lemma sp_193 : Nat.Prime 193 := prime_of_isPrimeSmall (by decide)

private lemma sp_197 : Nat.Prime 197 := prime_of_isPrimeSmall (by decide)

private lemma sp_199 : Nat.Prime 199 := prime_of_isPrimeSmall (by decide)

private lemma sp_211 : Nat.Prime 211 := prime_of_isPrimeSmall (by decide)

private lemma sp_223 : Nat.Prime 223 := prime_of_isPrimeSmall (by decide)

private lemma sp_227 : Nat.Prime 227 := prime_of_isPrimeSmall (by decide)

private lemma sp_229 : Nat.Prime 229 := prime_of_isPrimeSmall (by decide)

private lemma sp_233 : Nat.Prime 233 := prime_of_isPrimeSmall (by decide)

private lemma sp_239 : Nat.Prime 239 := prime_of_isPrimeSmall (by decide)

private lemma sp_241 : Nat.Prime 241 := prime_of_isPrimeSmall (by decide)

private lemma sp_257 : Nat.Prime 257 := prime_of_isPrimeSmall (by decide)

private lemma sp_263 : Nat.Prime 263 := prime_of_isPrimeSmall (by decide)

private lemma sp_269 : Nat.Prime 269 := prime_of_isPrimeSmall (by decide)

private lemma sp_271 : Nat.Prime 271 := prime_of_isPrimeSmall (by decide)

private lemma sp_277 : Nat.Prime 277 := prime_of_isPrimeSmall (by decide)

private lemma sp_281 : Nat.Prime 281 := prime_of_isPrimeSmall (by decide)

private lemma sp_283 : Nat.Prime 283 := prime_of_isPrimeSmall (by decide)

private lemma sp_293 : Nat.Prime 293 := prime_of_isPrimeSmall (by decide)

private lemma sp_307 : Nat.Prime 307 := prime_of_isPrimeSmall (by decide)

private lemma sp_311 : Nat.Prime 311 := prime_of_isPrimeSmall (by decide)

private lemma sp_313 : Nat.Prime 313 := prime_of_isPrimeSmall (by decide)

private lemma sp_317 : Nat.Prime 317 := prime_of_isPrimeSmall (by decide)

private lemma sp_331 : Nat.Prime 331 := prime_of_isPrimeSmall (by decide)

private lemma sp_337 : Nat.Prime 337 := prime_of_isPrimeSmall (by decide)

private lemma sp_347 : Nat.Prime 347 := prime_of_isPrimeSmall (by decide)

private lemma sp_353 : Nat.Prime 353 := prime_of_isPrimeSmall (by decide)

private lemma sp_367 : Nat.Prime 367 := prime_of_isPrimeSmall (by decide)

private lemma sp_373 : Nat.Prime 373 := prime_of_isPrimeSmall (by decide)

private lemma sp_397 : Nat.Prime 397 := prime_of_isPrimeSmall (by decide)

private lemma sp_401 : Nat.Prime 401 := prime_of_isPrimeSmall (by decide)

private lemma sp_409 : Nat.Prime 409 := prime_of_isPrimeSmall (by decide)

private lemma sp_421 : Nat.Prime 421 := prime_of_isPrimeSmall (by decide)

private lemma sp_431 : Nat.Prime 431 := prime_of_isPrimeSmall (by decide)

private lemma sp_433 : Nat.Prime 433 := prime_of_isPrimeSmall (by decide)

private lemma sp_439 : Nat.Prime 439 := prime_of_isPrimeSmall (by decide)

private lemma sp_443 : Nat.Prime 443 := prime_of_isPrimeSmall (by decide)

private lemma sp_449 : Nat.Prime 449 := prime_of_isPrimeSmall (by decide)

private lemma sp_457 : Nat.Prime 457 := prime_of_isPrimeSmall (by decide)

private lemma sp_463 : Nat.Prime 463 := prime_of_isPrimeSmall (by decide)

private lemma sp_467 : Nat.Prime 467 := prime_of_isPrimeSmall (by decide)

private lemma sp_479 : Nat.Prime 479 := prime_of_isPrimeSmall (by decide)

private lemma sp_487 : Nat.Prime 487 := prime_of_isPrimeSmall (by decide)

private lemma sp_503 : Nat.Prime 503 := prime_of_isPrimeSmall (by decide)

private lemma sp_509 : Nat.Prime 509 := prime_of_isPrimeSmall (by decide)

private lemma sp_523 : Nat.Prime 523 := prime_of_isPrimeSmall (by decide)

private lemma sp_541 : Nat.Prime 541 := prime_of_isPrimeSmall (by decide)

private lemma sp_547 : Nat.Prime 547 := prime_of_isPrimeSmall (by decide)

private lemma sp_563 : Nat.Prime 563 := prime_of_isPrimeSmall (by decide)

private lemma sp_569 : Nat.Prime 569 := prime_of_isPrimeSmall (by decide)

private lemma sp_571 : Nat.Prime 571 := prime_of_isPrimeSmall (by decide)

private lemma sp_577 : Nat.Prime 577 := prime_of_isPrimeSmall (by decide)

private lemma sp_593 : Nat.Prime 593 := prime_of_isPrimeSmall (by decide)

private lemma sp_607 : Nat.Prime 607 := prime_of_isPrimeSmall (by decide)

private lemma sp_613 : Nat.Prime 613 := prime_of_isPrimeSmall (by decide)

private lemma sp_619 : Nat.Prime 619 := prime_of_isPrimeSmall (by decide)

private lemma sp_631 : Nat.Prime 631 := prime_of_isPrimeSmall (by decide)

private lemma sp_641 : Nat.Prime 641 := prime_of_isPrimeSmall (by decide)

private lemma sp_643 : Nat.Prime 643 := prime_of_isPrimeSmall (by decide)

private lemma sp_647 : Nat.Prime 647 := prime_of_isPrimeSmall (by decide)

private lemma sp_653 : Nat.Prime 653 := prime_of_isPrimeSmall (by decide)

private lemma sp_659 : Nat.Prime 659 := prime_of_isPrimeSmall (by decide)

private lemma sp_661 : Nat.Prime 661 := prime_of_isPrimeSmall (by decide)

private lemma sp_677 : Nat.Prime 677 := prime_of_isPrimeSmall (by decide)

private lemma sp_683 : Nat.Prime 683 := prime_of_isPrimeSmall (by decide)

private lemma sp_691 : Nat.Prime 691 := prime_of_isPrimeSmall (by decide)

private lemma sp_709 : Nat.Prime 709 := prime_of_isPrimeSmall (by decide)

private lemma sp_719 : Nat.Prime 719 := prime_of_isPrimeSmall (by decide)

private lemma sp_739 : Nat.Prime 739 := prime_of_isPrimeSmall (by decide)

private lemma sp_757 : Nat.Prime 757 := prime_of_isPrimeSmall (by decide)

private lemma sp_773 : Nat.Prime 773 := prime_of_isPrimeSmall (by decide)

private lemma sp_809 : Nat.Prime 809 := prime_of_isPrimeSmall (by decide)

private lemma sp_811 : Nat.Prime 811 := prime_of_isPrimeSmall (by decide)

private lemma sp_857 : Nat.Prime 857 := prime_of_isPrimeSmall (by decide)

private lemma sp_883 : Nat.Prime 883 := prime_of_isPrimeSmall (by decide)

private lemma sp_907 : Nat.Prime 907 := prime_of_isPrimeSmall (by decide)

private lemma sp_911 : Nat.Prime 911 := prime_of_isPrimeSmall (by decide)

private lemma sp_941 : Nat.Prime 941 := prime_of_isPrimeSmall (by decide)

private lemma sp_953 : Nat.Prime 953 := prime_of_isPrimeSmall (by decide)

private lemma sp_967 : Nat.Prime 967 := prime_of_isPrimeSmall (by decide)

private lemma sp_971 : Nat.Prime 971 := prime_of_isPrimeSmall (by decide)

private lemma sp_991 : Nat.Prime 991 := prime_of_isPrimeSmall (by decide)

private lemma pr_0 : Nat.Prime 1667 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (7, 2), (17, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_17 all_primes_nil)))

private lemma pr_1 : Nat.Prime 13337 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (1667, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_0 all_primes_nil))

private lemma pr_2 : Nat.Prime 346763 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (13, 1), (13337, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_13 (all_primes_cons pr_1 all_primes_nil)))

private lemma pr_3 : Nat.Prime 1536160091 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (443, 1), (346763, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_443 (all_primes_cons pr_2 all_primes_nil))))

private lemma pr_4 : Nat.Prime 2069 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (11, 1), (47, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_47 all_primes_nil)))

private lemma pr_5 : Nat.Prime 3072320171 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (163, 1), (911, 1), (2069, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_163 (all_primes_cons sp_911 (all_primes_cons pr_4 all_primes_nil)))))

private lemma pr_6 : Nat.Prime 1733 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (433, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_433 all_primes_nil))

private lemma pr_7 : Nat.Prime 4608480251 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 3), (11, 1), (967, 1), (1733, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_11 (all_primes_cons sp_967 (all_primes_cons pr_6 all_primes_nil)))))

private lemma pr_8 : Nat.Prime 6144640331 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (53, 1), (71, 1), (283, 1), (577, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_53 (all_primes_cons sp_71 (all_primes_cons sp_283 (all_primes_cons sp_577 all_primes_nil))))))

private lemma pr_9 : Nat.Prime 2017 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 5), (3, 2), (7, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 all_primes_nil)))

private lemma pr_10 : Nat.Prime 8069 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (2017, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_9 all_primes_nil))

private lemma pr_11 : Nat.Prime 95189 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (53, 1), (449, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_53 (all_primes_cons sp_449 all_primes_nil)))

private lemma pr_12 : Nat.Prime 7680800411 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (8069, 1), (95189, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons pr_10 (all_primes_cons pr_11 all_primes_nil))))

private lemma pr_13 : Nat.Prime 1901 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (5, 2), (19, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_19 all_primes_nil)))

private lemma pr_14 : Nat.Prime 921696049 :=
  prime_of_lucasCheck (a := 11) (fs := [(2, 4), (3, 2), (7, 1), (13, 1), (37, 1), (1901, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_13 (all_primes_cons sp_37 (all_primes_cons pr_13 all_primes_nil))))))

private lemma pr_15 : Nat.Prime 9216960491 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (921696049, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons pr_14 all_primes_nil)))

private lemma pr_16 : Nat.Prime 16097 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 5), (503, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_503 all_primes_nil))

private lemma pr_17 : Nat.Prime 4088639 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (127, 1), (16097, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_127 (all_primes_cons pr_16 all_primes_nil)))

private lemma pr_18 : Nat.Prime 10753120571 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (263, 1), (4088639, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_263 (all_primes_cons pr_17 all_primes_nil))))

private lemma pr_19 : Nat.Prime 1327 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (13, 1), (17, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_13 (all_primes_cons sp_17 all_primes_nil))))

private lemma pr_20 : Nat.Prime 8053 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (11, 1), (61, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons sp_61 all_primes_nil))))

private lemma pr_21 : Nat.Prime 12289280651 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (5, 2), (23, 1), (1327, 1), (8053, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_23 (all_primes_cons pr_19 (all_primes_cons pr_20 all_primes_nil)))))

private lemma pr_22 : Nat.Prime 1382544073 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 3), (3, 3), (7, 1), (13, 1), (37, 1), (1901, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_13 (all_primes_cons sp_37 (all_primes_cons pr_13 all_primes_nil))))))

private lemma pr_23 : Nat.Prime 13825440731 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (5, 1), (1382544073, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons pr_22 all_primes_nil)))

private lemma pr_24 : Nat.Prime 438527 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (31, 1), (643, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_31 (all_primes_cons sp_643 all_primes_nil))))

private lemma pr_25 : Nat.Prime 15361600811 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (31, 1), (113, 1), (438527, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_31 (all_primes_cons sp_113 (all_primes_cons pr_24 all_primes_nil)))))

private lemma pr_26 : Nat.Prime 3181 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 2), (3, 1), (5, 1), (53, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_53 all_primes_nil))))

private lemma pr_27 : Nat.Prime 19087 :=
  prime_of_lucasCheck (a := 19) (fs := [(2, 1), (3, 1), (3181, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_26 all_primes_nil)))

private lemma pr_28 : Nat.Prime 4811701 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 2), (43, 1), (373, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_43 (all_primes_cons sp_373 all_primes_nil)))))

private lemma pr_29 : Nat.Prime 1653136865767 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 2), (19087, 1), (4811701, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_27 (all_primes_cons pr_28 all_primes_nil))))

private lemma pr_30 : Nat.Prime 9918821194603 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (1653136865767, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_29 all_primes_nil)))

private lemma pr_31 : Nat.Prime 19837642389193 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 3), (3, 3), (19087, 1), (4811701, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_27 (all_primes_cons pr_28 all_primes_nil))))

private lemma pr_32 : Nat.Prime 40763 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (89, 1), (229, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_89 (all_primes_cons sp_229 all_primes_nil)))

private lemma pr_33 : Nat.Prime 81527 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (40763, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_32 all_primes_nil))

private lemma pr_34 : Nat.Prime 29756463583783 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (3, 1), (13, 1), (67, 1), (211, 1), (331, 1), (81527, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_13 (all_primes_cons sp_67 (all_primes_cons sp_211 (all_primes_cons sp_331 (all_primes_cons pr_33 all_primes_nil)))))))

private lemma pr_35 : Nat.Prime 5701 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 2), (19, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_19 all_primes_nil))))

private lemma pr_36 : Nat.Prime 2467 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 2), (137, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_137 all_primes_nil)))

private lemma pr_37 : Nat.Prime 148021 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 2), (3, 1), (5, 1), (2467, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons pr_36 all_primes_nil))))

private lemma pr_38 : Nat.Prime 5063206327 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (5701, 1), (148021, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_35 (all_primes_cons pr_37 all_primes_nil))))

private lemma pr_39 : Nat.Prime 39675284778373 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (653, 1), (5063206327, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_653 (all_primes_cons pr_38 all_primes_nil))))

private lemma pr_40 : Nat.Prime 3299 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (17, 1), (97, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_17 (all_primes_cons sp_97 all_primes_nil)))

private lemma pr_41 : Nat.Prime 898033 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 4), (3, 1), (53, 1), (353, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_53 (all_primes_cons sp_353 all_primes_nil))))

private lemma pr_42 : Nat.Prime 835170691 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (5, 1), (31, 1), (898033, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_31 (all_primes_cons pr_41 all_primes_nil)))))

private lemma pr_43 : Nat.Prime 49594105972963 :=
  prime_of_lucasCheck (a := 14) (fs := [(2, 1), (3, 2), (3299, 1), (835170691, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_40 (all_primes_cons pr_42 all_primes_nil))))

private lemma pr_44 : Nat.Prime 37161391 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (5, 1), (7, 1), (311, 1), (569, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_311 (all_primes_cons sp_569 all_primes_nil))))))

private lemma pr_45 : Nat.Prime 59512927167553 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 6), (3, 1), (19, 1), (439, 1), (37161391, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_19 (all_primes_cons sp_439 (all_primes_cons pr_44 all_primes_nil)))))

private lemma pr_46 : Nat.Prime 2647 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 3), (7, 2)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 all_primes_nil)))

private lemma pr_47 : Nat.Prime 108149140751 :=
  prime_of_lucasCheck (a := 11) (fs := [(2, 1), (5, 3), (7, 1), (37, 1), (631, 1), (2647, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_37 (all_primes_cons sp_631 (all_primes_cons pr_46 all_primes_nil))))))

private lemma pr_48 : Nat.Prime 69431748362143 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (3, 1), (107, 1), (108149140751, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_107 (all_primes_cons pr_47 all_primes_nil))))

private lemma pr_49 : Nat.Prime 4111 :=
  prime_of_lucasCheck (a := 12) (fs := [(2, 1), (3, 1), (5, 1), (137, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_137 all_primes_nil))))

private lemma pr_50 : Nat.Prime 133887049 :=
  prime_of_lucasCheck (a := 11) (fs := [(2, 3), (3, 1), (23, 1), (59, 1), (4111, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_23 (all_primes_cons sp_59 (all_primes_cons pr_49 all_primes_nil)))))

private lemma pr_51 : Nat.Prime 79350569556733 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 2), (3, 2), (101, 1), (163, 1), (133887049, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_101 (all_primes_cons sp_163 (all_primes_cons pr_50 all_primes_nil)))))

private lemma pr_52 : Nat.Prime 248827 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (113, 1), (367, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_113 (all_primes_cons sp_367 all_primes_nil))))

private lemma pr_53 : Nat.Prime 357813227 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (719, 1), (248827, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_719 (all_primes_cons pr_52 all_primes_nil)))

private lemma pr_54 : Nat.Prime 89269390751323 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (43, 1), (967, 1), (357813227, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_43 (all_primes_cons sp_967 (all_primes_cons pr_53 all_primes_nil)))))

private lemma pr_55 : Nat.Prime 45673 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 3), (3, 1), (11, 1), (173, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons sp_173 all_primes_nil))))

private lemma pr_56 : Nat.Prime 4132842164413 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (13, 1), (37, 1), (61, 1), (257, 1), (45673, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_13 (all_primes_cons sp_37 (all_primes_cons sp_61 (all_primes_cons sp_257 (all_primes_cons pr_55 all_primes_nil)))))))

private lemma pr_57 : Nat.Prime 99188211945913 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 3), (3, 1), (4132842164413, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_56 all_primes_nil)))

private lemma pr_58 : Nat.Prime 1201 :=
  prime_of_lucasCheck (a := 11) (fs := [(2, 4), (3, 1), (5, 2)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 all_primes_nil)))

private lemma pr_59 : Nat.Prime 7207 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (1201, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_58 all_primes_nil)))

private lemma pr_60 : Nat.Prime 974674681 :=
  prime_of_lucasCheck (a := 22) (fs := [(2, 3), (3, 1), (5, 1), (7, 2), (23, 1), (7207, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_23 (all_primes_cons pr_59 all_primes_nil))))))

private lemma pr_61 : Nat.Prime 109107033140503 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 4), (691, 1), (974674681, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_691 (all_primes_cons pr_60 all_primes_nil))))

private lemma pr_62 : Nat.Prime 56197 :=
  prime_of_lucasCheck (a := 13) (fs := [(2, 2), (3, 2), (7, 1), (223, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_223 all_primes_nil))))

private lemma pr_63 : Nat.Prime 28997653 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (43, 1), (56197, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_43 (all_primes_cons pr_62 all_primes_nil))))

private lemma pr_64 : Nat.Prime 431253095417 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (11, 1), (13, 2), (28997653, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_13 (all_primes_cons pr_63 all_primes_nil))))

private lemma pr_65 : Nat.Prime 119025854335093 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (23, 1), (431253095417, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_23 (all_primes_cons pr_64 all_primes_nil))))

private lemma pr_66 : Nat.Prime 72101 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (5, 2), (7, 1), (103, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_103 all_primes_nil))))

private lemma pr_67 : Nat.Prime 20765089 :=
  prime_of_lucasCheck (a := 13) (fs := [(2, 5), (3, 2), (72101, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_66 all_primes_nil)))

private lemma pr_68 : Nat.Prime 4621 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 1), (7, 1), (11, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_11 all_primes_nil)))))

private lemma pr_69 : Nat.Prime 409753313 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 5), (17, 1), (163, 1), (4621, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_17 (all_primes_cons sp_163 (all_primes_cons pr_68 all_primes_nil))))

private lemma pr_70 : Nat.Prime 10686756399687260393 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (157, 1), (20765089, 1), (409753313, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_157 (all_primes_cons pr_67 (all_primes_cons pr_69 all_primes_nil))))

private lemma pr_71 : Nat.Prime 341976204789992332577 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 5), (10686756399687260393, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_70 all_primes_nil))

private lemma pr_72 : Nat.Prime 2609 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (163, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_163 all_primes_nil))

private lemma pr_73 : Nat.Prime 20788513 :=
  prime_of_lucasCheck (a := 10) (fs := [(2, 5), (3, 1), (83, 1), (2609, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_83 (all_primes_cons pr_72 all_primes_nil))))

private lemma pr_74 : Nat.Prime 358289 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 4), (7, 2), (457, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_457 all_primes_nil)))

private lemma pr_75 : Nat.Prime 8598937 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 3), (3, 1), (358289, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_74 all_primes_nil)))

private lemma pr_76 : Nat.Prime 34395749 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (8598937, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_75 all_primes_nil))

private lemma pr_77 : Nat.Prime 683952409579984665137 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (191, 1), (313, 1), (20788513, 1), (34395749, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_191 (all_primes_cons sp_313 (all_primes_cons pr_73 (all_primes_cons pr_76 all_primes_nil)))))

private lemma pr_78 : Nat.Prime 3407 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (13, 1), (131, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_13 (all_primes_cons sp_131 all_primes_nil)))

private lemma pr_79 : Nat.Prime 149909 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (11, 1), (3407, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_78 all_primes_nil)))

private lemma pr_80 : Nat.Prime 16235144701 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 2), (19, 2), (149909, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_19 (all_primes_cons pr_79 all_primes_nil)))))

private lemma pr_81 : Nat.Prime 5106764765699551 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 3), (5, 2), (233, 1), (16235144701, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_233 (all_primes_cons pr_80 all_primes_nil)))))

private lemma pr_82 : Nat.Prime 1025928614369976997697 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 6), (43, 1), (73, 1), (5106764765699551, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_43 (all_primes_cons sp_73 (all_primes_cons pr_81 all_primes_nil))))

private lemma pr_83 : Nat.Prime 72641729 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 6), (23, 1), (61, 1), (809, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_23 (all_primes_cons sp_61 (all_primes_cons sp_809 all_primes_nil))))

private lemma pr_84 : Nat.Prime 31115893 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 2), (3, 1), (59, 1), (71, 1), (619, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_59 (all_primes_cons sp_71 (all_primes_cons sp_619 all_primes_nil)))))

private lemma pr_85 : Nat.Prime 5974251457 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 6), (3, 1), (31115893, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_84 all_primes_nil)))

private lemma pr_86 : Nat.Prime 1367904819159969330257 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (197, 1), (72641729, 1), (5974251457, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_197 (all_primes_cons pr_83 (all_primes_cons pr_85 all_primes_nil))))

private lemma pr_87 : Nat.Prime 860256101 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (5, 2), (11, 1), (17, 1), (179, 1), (257, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_11 (all_primes_cons sp_17 (all_primes_cons sp_179 (all_primes_cons sp_257 all_primes_nil))))))

private lemma pr_88 : Nat.Prime 1297 :=
  prime_of_lucasCheck (a := 10) (fs := [(2, 4), (3, 4)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 all_primes_nil))

private lemma pr_89 : Nat.Prime 169709857 :=
  prime_of_lucasCheck (a := 10) (fs := [(2, 5), (3, 1), (29, 1), (47, 1), (1297, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_29 (all_primes_cons sp_47 (all_primes_cons pr_88 all_primes_nil)))))

private lemma pr_90 : Nat.Prime 62113807663 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (61, 1), (169709857, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_61 (all_primes_cons pr_89 all_primes_nil))))

private lemma pr_91 : Nat.Prime 1709881023949961662817 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 5), (860256101, 1), (62113807663, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_87 (all_primes_cons pr_90 all_primes_nil)))

private lemma pr_92 : Nat.Prime 10337 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 5), (17, 1), (19, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_17 (all_primes_cons sp_19 all_primes_nil)))

private lemma pr_93 : Nat.Prime 63050510827 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 2), (17, 1), (31, 1), (643, 1), (10337, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_17 (all_primes_cons sp_31 (all_primes_cons sp_643 (all_primes_cons pr_92 all_primes_nil))))))

private lemma pr_94 : Nat.Prime 716430596627078909 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (691, 1), (4111, 1), (63050510827, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_691 (all_primes_cons pr_49 (all_primes_cons pr_93 all_primes_nil))))

private lemma pr_95 : Nat.Prime 2051857228739953995377 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (179, 1), (716430596627078909, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_179 (all_primes_cons pr_94 all_primes_nil)))

private lemma pr_96 : Nat.Prime 84299 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (113, 1), (373, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_113 (all_primes_cons sp_373 all_primes_nil)))

private lemma pr_97 : Nat.Prime 640691 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (5, 1), (79, 1), (811, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_79 (all_primes_cons sp_811 all_primes_nil))))

private lemma pr_98 : Nat.Prime 1281383 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (640691, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_97 all_primes_nil))

private lemma pr_99 : Nat.Prime 30753193 :=
  prime_of_lucasCheck (a := 10) (fs := [(2, 3), (3, 1), (1281383, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_98 all_primes_nil)))

private lemma pr_100 : Nat.Prime 2337242669 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 2), (19, 1), (30753193, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_19 (all_primes_cons pr_99 all_primes_nil)))

private lemma pr_101 : Nat.Prime 46744853381 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (5, 1), (2337242669, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons pr_100 all_primes_nil)))

private lemma pr_102 : Nat.Prime 165502864596926599 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (7, 1), (84299, 1), (46744853381, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons pr_96 (all_primes_cons pr_101 all_primes_nil)))))

private lemma pr_103 : Nat.Prime 2393833433529946327937 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 7), (113, 1), (165502864596926599, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_113 (all_primes_cons pr_102 all_primes_nil)))

private lemma pr_104 : Nat.Prime 1063 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 2), (59, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_59 all_primes_nil)))

private lemma pr_105 : Nat.Prime 4253 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (1063, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_104 all_primes_nil))

private lemma pr_106 : Nat.Prime 1939369 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 3), (3, 1), (19, 1), (4253, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_19 (all_primes_cons pr_105 all_primes_nil))))

private lemma pr_107 : Nat.Prime 1497192869 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (193, 1), (1939369, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_193 (all_primes_cons pr_106 all_primes_nil)))

private lemma pr_108 : Nat.Prime 2735809638319938660497 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (23, 1), (101, 2), (677, 1), (719, 1), (1497192869, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_23 (all_primes_cons sp_101 (all_primes_cons sp_677 (all_primes_cons sp_719 (all_primes_cons pr_107 all_primes_nil))))))

private lemma pr_109 : Nat.Prime 88301 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (5, 2), (883, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_883 all_primes_nil)))

private lemma pr_110 : Nat.Prime 529807 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (88301, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_109 all_primes_nil)))

private lemma pr_111 : Nat.Prime 4327 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (7, 1), (103, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_103 all_primes_nil))))

private lemma pr_112 : Nat.Prime 250967 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (29, 1), (4327, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_29 (all_primes_cons pr_111 all_primes_nil)))

private lemma pr_113 : Nat.Prime 1918391749 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (7, 2), (13, 1), (250967, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_13 (all_primes_cons pr_112 all_primes_nil)))))

private lemma pr_114 : Nat.Prime 3077785843109930993057 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 5), (173, 1), (547, 1), (529807, 1), (1918391749, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_173 (all_primes_cons sp_547 (all_primes_cons pr_110 (all_primes_cons pr_113 all_primes_nil)))))

private lemma pr_115 : Nat.Prime 38651 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 2), (773, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_773 all_primes_nil)))

private lemma pr_116 : Nat.Prime 13613 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (41, 1), (83, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_41 (all_primes_cons sp_83 all_primes_nil)))

private lemma pr_117 : Nat.Prime 14865397 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 2), (3, 1), (7, 1), (13, 1), (13613, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_13 (all_primes_cons pr_116 all_primes_nil)))))

private lemma pr_118 : Nat.Prime 920783 :=
  prime_of_lucasCheck (a := 10) (fs := [(2, 1), (23, 1), (37, 1), (541, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_23 (all_primes_cons sp_37 (all_primes_cons sp_541 all_primes_nil))))

private lemma pr_119 : Nat.Prime 371996333 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (101, 1), (920783, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_101 (all_primes_cons pr_118 all_primes_nil)))

private lemma pr_120 : Nat.Prime 3419762047899923325617 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (38651, 1), (14865397, 1), (371996333, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_115 (all_primes_cons pr_117 (all_primes_cons pr_119 all_primes_nil))))

private lemma pr_121 : Nat.Prime 37049 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 3), (11, 1), (421, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_421 all_primes_nil)))

private lemma pr_122 : Nat.Prime 24109 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (7, 2), (41, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_41 all_primes_nil))))

private lemma pr_123 : Nat.Prime 48731 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (5, 1), (11, 1), (443, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_11 (all_primes_cons sp_443 all_primes_nil))))

private lemma pr_124 : Nat.Prime 97463 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (48731, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_123 all_primes_nil))

private lemma pr_125 : Nat.Prime 1586470895254391 :=
  prime_of_lucasCheck (a := 11) (fs := [(2, 1), (5, 1), (107, 1), (631, 1), (24109, 1), (97463, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_107 (all_primes_cons sp_631 (all_primes_cons pr_122 (all_primes_cons pr_124 all_primes_nil))))))

private lemma pr_126 : Nat.Prime 3761738252689915658177 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 6), (37049, 1), (1586470895254391, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_121 (all_primes_cons pr_125 all_primes_nil)))

private lemma pr_127 : Nat.Prime 19421 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 2), (5, 1), (971, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_971 all_primes_nil)))

private lemma pr_128 : Nat.Prime 699157 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 2), (19421, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_127 all_primes_nil)))

private lemma pr_129 : Nat.Prime 740681761 :=
  prime_of_lucasCheck (a := 17) (fs := [(2, 5), (3, 1), (5, 1), (7, 1), (13, 1), (31, 1), (547, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_13 (all_primes_cons sp_31 (all_primes_cons sp_547 all_primes_nil)))))))

private lemma pr_130 : Nat.Prime 312783114137188109 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (151, 1), (699157, 1), (740681761, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_151 (all_primes_cons pr_128 (all_primes_cons pr_129 all_primes_nil))))

private lemma pr_131 : Nat.Prime 6255662282743762181 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (5, 1), (312783114137188109, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons pr_130 all_primes_nil)))

private lemma pr_132 : Nat.Prime 4103714457479907990737 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (41, 1), (6255662282743762181, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_41 (all_primes_cons pr_131 all_primes_nil)))

private lemma pr_133 : Nat.Prime 1907 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (953, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_953 all_primes_nil))

private lemma pr_134 : Nat.Prime 1013 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 2), (11, 1), (23, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_23 all_primes_nil)))

private lemma pr_135 : Nat.Prime 2027 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (1013, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_134 all_primes_nil))

private lemma pr_136 : Nat.Prime 1447 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (241, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_241 all_primes_nil)))

private lemma pr_137 : Nat.Prime 2797 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (233, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_233 all_primes_nil)))

private lemma pr_138 : Nat.Prime 57139202563 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (3, 1), (13, 1), (181, 1), (1447, 1), (2797, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_13 (all_primes_cons sp_181 (all_primes_cons pr_136 (all_primes_cons pr_137 all_primes_nil))))))

private lemma pr_139 : Nat.Prime 4445690662269900323297 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 5), (17, 1), (37, 1), (1907, 1), (2027, 1), (57139202563, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_17 (all_primes_cons sp_37 (all_primes_cons pr_133 (all_primes_cons pr_135 (all_primes_cons pr_138 all_primes_nil))))))

private lemma pr_140 : Nat.Prime 3457 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 7), (3, 3)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 all_primes_nil))

private lemma pr_141 : Nat.Prime 4129 :=
  prime_of_lucasCheck (a := 13) (fs := [(2, 5), (3, 1), (43, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_43 all_primes_nil)))

private lemma pr_142 : Nat.Prime 12064939 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (487, 1), (4129, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_487 (all_primes_cons pr_141 all_primes_nil))))

private lemma pr_143 : Nat.Prime 22003 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (19, 1), (193, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_19 (all_primes_cons sp_193 all_primes_nil))))

private lemma pr_144 : Nat.Prime 52367141 :=
  prime_of_lucasCheck (a := 10) (fs := [(2, 2), (5, 1), (7, 1), (17, 1), (22003, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_17 (all_primes_cons pr_143 all_primes_nil)))))

private lemma pr_145 : Nat.Prime 4787666867059892655857 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (137, 1), (3457, 1), (12064939, 1), (52367141, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_137 (all_primes_cons pr_140 (all_primes_cons pr_142 (all_primes_cons pr_144 all_primes_nil)))))

private lemma pr_146 : Nat.Prime 2689 :=
  prime_of_lucasCheck (a := 19) (fs := [(2, 7), (3, 1), (7, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 all_primes_nil)))

private lemma pr_147 : Nat.Prime 451753 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 3), (3, 1), (7, 1), (2689, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons pr_146 all_primes_nil))))

private lemma pr_148 : Nat.Prime 867365761 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 7), (3, 1), (5, 1), (451753, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons pr_147 all_primes_nil))))

private lemma pr_149 : Nat.Prime 2013751 :=
  prime_of_lucasCheck (a := 11) (fs := [(2, 1), (3, 2), (5, 4), (179, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_179 all_primes_nil))))

private lemma pr_150 : Nat.Prime 5775437869 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (239, 1), (2013751, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_239 (all_primes_cons pr_149 all_primes_nil))))

private lemma pr_151 : Nat.Prime 5129643071849884988417 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 10), (867365761, 1), (5775437869, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_148 (all_primes_cons pr_150 all_primes_nil)))

private lemma pr_152 : Nat.Prime 1218901 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 2), (17, 1), (239, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_17 (all_primes_cons sp_239 all_primes_nil)))))

private lemma pr_153 : Nat.Prime 224351 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (5, 2), (7, 1), (641, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_641 all_primes_nil))))

private lemma pr_154 : Nat.Prime 448703 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (224351, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_153 all_primes_nil))

private lemma pr_155 : Nat.Prime 719719613 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (401, 1), (448703, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_401 (all_primes_cons pr_154 all_primes_nil)))

private lemma pr_156 : Nat.Prime 280561099539661 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 1), (73, 1), (89, 1), (719719613, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_73 (all_primes_cons sp_89 (all_primes_cons pr_155 all_primes_nil))))))

private lemma pr_157 : Nat.Prime 5471619276639877320977 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (1218901, 1), (280561099539661, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_152 (all_primes_cons pr_156 all_primes_nil)))

private lemma pr_158 : Nat.Prime 2687 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (17, 1), (79, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_17 (all_primes_cons sp_79 all_primes_nil)))

private lemma pr_159 : Nat.Prime 221570021 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (5, 1), (7, 1), (19, 1), (31, 1), (2687, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_19 (all_primes_cons sp_31 (all_primes_cons pr_158 all_primes_nil))))))

private lemma pr_160 : Nat.Prime 22194587 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (23, 1), (563, 1), (857, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_23 (all_primes_cons sp_563 (all_primes_cons sp_857 all_primes_nil))))

private lemma pr_161 : Nat.Prime 46608632701 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 2), (7, 1), (22194587, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons pr_160 all_primes_nil)))))

private lemma pr_162 : Nat.Prime 2166703103992332274919569 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 4), (3, 2), (31, 1), (47, 1), (221570021, 1), (46608632701, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_31 (all_primes_cons sp_47 (all_primes_cons pr_159 (all_primes_cons pr_161 all_primes_nil))))))

private lemma pr_163 : Nat.Prime 3821 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 2), (5, 1), (191, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_191 all_primes_nil)))

private lemma pr_164 : Nat.Prime 7643 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3821, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_163 all_primes_nil))

private lemma pr_165 : Nat.Prime 15287 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (7643, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_164 all_primes_nil))

private lemma pr_166 : Nat.Prime 5107 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (23, 1), (37, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_23 (all_primes_cons sp_37 all_primes_nil))))

private lemma pr_167 : Nat.Prime 7757 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (7, 1), (277, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_277 all_primes_nil)))

private lemma pr_168 : Nat.Prime 28530247 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (3, 1), (613, 1), (7757, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_613 (all_primes_cons pr_167 all_primes_nil))))

private lemma pr_169 : Nat.Prime 25061083085789 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (43, 1), (5107, 1), (28530247, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_43 (all_primes_cons pr_166 (all_primes_cons pr_168 all_primes_nil))))

private lemma pr_170 : Nat.Prime 20687873965152647923 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 3), (15287, 1), (25061083085789, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_165 (all_primes_cons pr_169 all_primes_nil))))

private lemma pr_171 : Nat.Prime 4333406207984664549839119 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 5), (431, 1), (20687873965152647923, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_431 (all_primes_cons pr_170 all_primes_nil))))

private lemma pr_172 : Nat.Prime 3079 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (3, 4), (19, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_19 all_primes_nil)))

private lemma pr_173 : Nat.Prime 14409721 :=
  prime_of_lucasCheck (a := 17) (fs := [(2, 3), (3, 2), (5, 1), (13, 1), (3079, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_13 (all_primes_cons pr_172 all_primes_nil)))))

private lemma pr_174 : Nat.Prime 1583 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (7, 1), (113, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_113 all_primes_nil)))

private lemma pr_175 : Nat.Prime 54023017 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 3), (3, 1), (107, 1), (109, 1), (193, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_107 (all_primes_cons sp_109 (all_primes_cons sp_193 all_primes_nil)))))

private lemma pr_176 : Nat.Prime 171036871823 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (1583, 1), (54023017, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_174 (all_primes_cons pr_175 all_primes_nil)))

private lemma pr_177 : Nat.Prime 6500109311976996824758669 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 2), (3, 2), (61, 1), (1201, 1), (14409721, 1), (171036871823, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_61 (all_primes_cons pr_58 (all_primes_cons pr_173 (all_primes_cons pr_176 all_primes_nil))))))

private lemma pr_178 : Nat.Prime 1039 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (173, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_173 all_primes_nil)))

private lemma pr_179 : Nat.Prime 222347 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (107, 1), (1039, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_107 (all_primes_cons pr_178 all_primes_nil)))

private lemma pr_180 : Nat.Prime 4002247 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (3, 2), (222347, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_179 all_primes_nil)))

private lemma pr_181 : Nat.Prime 5347 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 5), (11, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 all_primes_nil)))

private lemma pr_182 : Nat.Prime 213881 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (5, 1), (5347, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons pr_181 all_primes_nil)))

private lemma pr_183 : Nat.Prime 7699717 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 2), (213881, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_182 all_primes_nil)))

private lemma pr_184 : Nat.Prime 1931 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (193, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_193 all_primes_nil)))

private lemma pr_185 : Nat.Prime 3863 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (1931, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_184 all_primes_nil))

private lemma pr_186 : Nat.Prime 46363727 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (17, 1), (353, 1), (3863, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_17 (all_primes_cons sp_353 (all_primes_cons pr_185 all_primes_nil))))

private lemma pr_187 : Nat.Prime 8666812415969329099678219 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 2), (337, 1), (4002247, 1), (7699717, 1), (46363727, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_337 (all_primes_cons pr_180 (all_primes_cons pr_183 (all_primes_cons pr_186 all_primes_nil))))))

private lemma pr_188 : Nat.Prime 1811 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (5, 1), (181, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_181 all_primes_nil)))

private lemma pr_189 : Nat.Prime 3623 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (1811, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_188 all_primes_nil))

private lemma pr_190 : Nat.Prime 7879 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (13, 1), (101, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_13 (all_primes_cons sp_101 all_primes_nil))))

private lemma pr_191 : Nat.Prime 2955862801 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 4), (3, 3), (5, 2), (11, 1), (139, 1), (179, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_11 (all_primes_cons sp_139 (all_primes_cons sp_179 all_primes_nil))))))

private lemma pr_192 : Nat.Prime 1757018054444819 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (11, 1), (41, 1), (659, 1), (2955862801, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_41 (all_primes_cons sp_659 (all_primes_cons pr_191 all_primes_nil)))))

private lemma pr_193 : Nat.Prime 10833515519961661374597769 :=
  prime_of_lucasCheck (a := 13) (fs := [(2, 3), (3, 3), (3623, 1), (7879, 1), (1757018054444819, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_189 (all_primes_cons pr_190 (all_primes_cons pr_192 all_primes_nil)))))

private lemma pr_194 : Nat.Prime 31151 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (5, 2), (7, 1), (89, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_89 all_primes_nil))))

private lemma pr_195 : Nat.Prime 6167899 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 2), (11, 1), (31151, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons pr_194 all_primes_nil))))

private lemma pr_196 : Nat.Prime 1979 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (23, 1), (43, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_23 (all_primes_cons sp_43 all_primes_nil)))

private lemma pr_197 : Nat.Prime 1693 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 2), (47, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_47 all_primes_nil)))

private lemma pr_198 : Nat.Prime 101581 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 1), (1693, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons pr_197 all_primes_nil))))

private lemma pr_199 : Nat.Prime 609487 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (101581, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_198 all_primes_nil)))

private lemma pr_200 : Nat.Prime 14627689 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 3), (3, 1), (609487, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_199 all_primes_nil)))

private lemma pr_201 : Nat.Prime 117095686553467249 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 4), (3, 1), (11, 1), (47, 1), (163, 1), (1979, 1), (14627689, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons sp_47 (all_primes_cons sp_163 (all_primes_cons pr_196 (all_primes_cons pr_200 all_primes_nil)))))))

private lemma pr_202 : Nat.Prime 13000218623953993649517319 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 2), (6167899, 1), (117095686553467249, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_195 (all_primes_cons pr_201 all_primes_nil))))

private lemma pr_203 : Nat.Prime 10267 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (29, 1), (59, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_29 (all_primes_cons sp_59 all_primes_nil))))

private lemma pr_204 : Nat.Prime 61603 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (10267, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_203 all_primes_nil)))

private lemma pr_205 : Nat.Prime 322051 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (5, 2), (19, 1), (113, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_19 (all_primes_cons sp_113 all_primes_nil)))))

private lemma pr_206 : Nat.Prime 153940379 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (239, 1), (322051, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_239 (all_primes_cons pr_205 all_primes_nil)))

private lemma pr_207 : Nat.Prime 307880759 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (153940379, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_206 all_primes_nil))

private lemma pr_208 : Nat.Prime 4099 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (683, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_683 all_primes_nil)))

private lemma pr_209 : Nat.Prime 600355937 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 5), (23, 1), (199, 1), (4099, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_23 (all_primes_cons sp_199 (all_primes_cons pr_208 all_primes_nil))))

private lemma pr_210 : Nat.Prime 15166921727946325924436869 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 2), (3, 2), (37, 1), (61603, 1), (307880759, 1), (600355937, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_37 (all_primes_cons pr_204 (all_primes_cons pr_207 (all_primes_cons pr_209 all_primes_nil))))))

private lemma pr_211 : Nat.Prime 9623 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (17, 1), (283, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_17 (all_primes_cons sp_283 all_primes_nil)))

private lemma pr_212 : Nat.Prime 12144227 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (631, 1), (9623, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_631 (all_primes_cons pr_211 all_primes_nil)))

private lemma pr_213 : Nat.Prime 218596087 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 2), (12144227, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_212 all_primes_nil)))

private lemma pr_214 : Nat.Prime 1783 :=
  prime_of_lucasCheck (a := 10) (fs := [(2, 1), (3, 4), (11, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 all_primes_nil)))

private lemma pr_215 : Nat.Prime 92717 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (13, 1), (1783, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_13 (all_primes_cons pr_214 all_primes_nil)))

private lemma pr_216 : Nat.Prime 1307 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (653, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_653 all_primes_nil))

private lemma pr_217 : Nat.Prime 258787 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 2), (11, 1), (1307, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons pr_216 all_primes_nil))))

private lemma pr_218 : Nat.Prime 4318911770221 :=
  prime_of_lucasCheck (a := 10) (fs := [(2, 2), (3, 2), (5, 1), (92717, 1), (258787, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons pr_215 (all_primes_cons pr_217 all_primes_nil)))))

private lemma pr_219 : Nat.Prime 1468430001875141 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 2), (5, 1), (17, 1), (4318911770221, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_17 (all_primes_cons pr_218 all_primes_nil))))

private lemma pr_220 : Nat.Prime 17333624831938658199356419 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 3), (218596087, 1), (1468430001875141, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_213 (all_primes_cons pr_219 all_primes_nil))))

private lemma pr_221 : Nat.Prime 6529 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 7), (3, 1), (17, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_17 all_primes_nil)))

private lemma pr_222 : Nat.Prime 378683 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (29, 1), (6529, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_29 (all_primes_cons pr_221 all_primes_nil)))

private lemma pr_223 : Nat.Prime 4656286169 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (29, 1), (53, 1), (378683, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_29 (all_primes_cons sp_53 (all_primes_cons pr_222 all_primes_nil))))

private lemma pr_224 : Nat.Prime 18583 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (19, 1), (163, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_19 (all_primes_cons sp_163 all_primes_nil))))

private lemma pr_225 : Nat.Prime 42901 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 2), (3, 1), (5, 2), (11, 1), (13, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_11 (all_primes_cons sp_13 all_primes_nil)))))

private lemma pr_226 : Nat.Prime 257407 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (42901, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_225 all_primes_nil)))

private lemma pr_227 : Nat.Prime 3635379653561 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 3), (5, 1), (19, 1), (18583, 1), (257407, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_19 (all_primes_cons pr_224 (all_primes_cons pr_226 all_primes_nil)))))

private lemma pr_228 : Nat.Prime 19500327935930990474275969 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 7), (3, 2), (4656286169, 1), (3635379653561, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_223 (all_primes_cons pr_227 all_primes_nil))))

private lemma pr_229 : Nat.Prime 6037 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 2), (3, 1), (503, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_503 all_primes_nil)))

private lemma pr_230 : Nat.Prime 144889 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 3), (3, 1), (6037, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_229 all_primes_nil)))

private lemma pr_231 : Nat.Prime 1312404563 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (7, 1), (647, 1), (144889, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_647 (all_primes_cons pr_230 all_primes_nil))))

private lemma pr_232 : Nat.Prime 3527 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (41, 1), (43, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_41 (all_primes_cons sp_43 all_primes_nil)))

private lemma pr_233 : Nat.Prime 387971 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (5, 1), (11, 1), (3527, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_11 (all_primes_cons pr_232 all_primes_nil))))

private lemma pr_234 : Nat.Prime 3103769 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (387971, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_233 all_primes_nil))

private lemma pr_235 : Nat.Prime 646819252063 :=
  prime_of_lucasCheck (a := 17) (fs := [(2, 1), (3, 1), (47, 1), (739, 1), (3103769, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_47 (all_primes_cons sp_739 (all_primes_cons pr_234 all_primes_nil)))))

private lemma pr_236 : Nat.Prime 1697777075687456726939 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (1312404563, 1), (646819252063, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_231 (all_primes_cons pr_235 all_primes_nil)))

private lemma pr_237 : Nat.Prime 21667031039923322749195519 :=
  prime_of_lucasCheck (a := 15) (fs := [(2, 1), (3, 2), (709, 1), (1697777075687456726939, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_709 (all_primes_cons pr_236 all_primes_nil))))

private lemma pr_238 : Nat.Prime 30559 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (3, 1), (11, 1), (463, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons sp_463 all_primes_nil))))

private lemma pr_239 : Nat.Prime 1039007 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (17, 1), (30559, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_17 (all_primes_cons pr_238 all_primes_nil)))

private lemma pr_240 : Nat.Prime 1028616931 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 2), (5, 1), (11, 1), (1039007, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_11 (all_primes_cons pr_239 all_primes_nil)))))

private lemma pr_241 : Nat.Prime 5573 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (7, 1), (199, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_199 all_primes_nil)))

private lemma pr_242 : Nat.Prime 14311464001 :=
  prime_of_lucasCheck (a := 11) (fs := [(2, 6), (3, 1), (5, 3), (107, 1), (5573, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_107 (all_primes_cons pr_241 all_primes_nil)))))

private lemma pr_243 : Nat.Prime 23833734143915655024115069 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 2), (3, 4), (19, 1), (263, 1), (1028616931, 1), (14311464001, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_19 (all_primes_cons sp_263 (all_primes_cons pr_240 (all_primes_cons pr_242 all_primes_nil))))))

private lemma pr_244 : Nat.Prime 1223 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (13, 1), (47, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_13 (all_primes_cons sp_47 all_primes_nil)))

private lemma pr_245 : Nat.Prime 2447 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (1223, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_244 all_primes_nil))

private lemma pr_246 : Nat.Prime 35687551 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (5, 2), (53, 1), (67, 2)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_53 (all_primes_cons sp_67 all_primes_nil)))))

private lemma pr_247 : Nat.Prime 1759 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (3, 1), (293, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_293 all_primes_nil)))

private lemma pr_248 : Nat.Prime 8951 :=
  prime_of_lucasCheck (a := 13) (fs := [(2, 1), (5, 2), (179, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_179 all_primes_nil)))

private lemma pr_249 : Nat.Prime 53185964803 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (563, 1), (1759, 1), (8951, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_563 (all_primes_cons pr_247 (all_primes_cons pr_248 all_primes_nil)))))

private lemma pr_250 : Nat.Prime 26000437247907987299034619 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 2), (311, 1), (2447, 1), (35687551, 1), (53185964803, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_311 (all_primes_cons pr_245 (all_primes_cons pr_246 (all_primes_cons pr_249 all_primes_nil))))))

private lemma pr_251 : Nat.Prime 673313 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 5), (53, 1), (397, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_53 (all_primes_cons sp_397 all_primes_nil)))

private lemma pr_252 : Nat.Prime 30269 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 2), (7, 1), (23, 1), (47, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_23 (all_primes_cons sp_47 all_primes_nil))))

private lemma pr_253 : Nat.Prime 60539 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (30269, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_252 all_primes_nil))

private lemma pr_254 : Nat.Prime 3465271 :=
  prime_of_lucasCheck (a := 15) (fs := [(2, 1), (3, 2), (5, 1), (139, 1), (277, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_139 (all_primes_cons sp_277 all_primes_nil)))))

private lemma pr_255 : Nat.Prime 540582277 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (13, 1), (3465271, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_13 (all_primes_cons pr_254 all_primes_nil))))

private lemma pr_256 : Nat.Prime 581022916036497463 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (11, 1), (269, 1), (60539, 1), (540582277, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons sp_269 (all_primes_cons pr_253 (all_primes_cons pr_255 all_primes_nil))))))

private lemma pr_257 : Nat.Prime 28167140351900319573954169 :=
  prime_of_lucasCheck (a := 11) (fs := [(2, 3), (3, 2), (673313, 1), (581022916036497463, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_251 (all_primes_cons pr_256 all_primes_nil))))

private lemma pr_258 : Nat.Prime 9043 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (11, 1), (137, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons sp_137 all_primes_nil))))

private lemma pr_259 : Nat.Prime 47964073 :=
  prime_of_lucasCheck (a := 23) (fs := [(2, 3), (3, 1), (13, 1), (17, 1), (9043, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_13 (all_primes_cons sp_17 (all_primes_cons pr_258 all_primes_nil)))))

private lemma pr_260 : Nat.Prime 75629 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (7, 1), (37, 1), (73, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_37 (all_primes_cons sp_73 all_primes_nil))))

private lemma pr_261 : Nat.Prime 40990919 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (271, 1), (75629, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_271 (all_primes_cons pr_260 all_primes_nil)))

private lemma pr_262 : Nat.Prime 107446216701181 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 1), (7, 1), (79, 2), (40990919, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_79 (all_primes_cons pr_261 all_primes_nil))))))

private lemma pr_263 : Nat.Prime 30333843455892651848873719 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 3), (109, 1), (47964073, 1), (107446216701181, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_109 (all_primes_cons pr_259 (all_primes_cons pr_262 all_primes_nil)))))

private lemma pr_264 : Nat.Prime 41809 :=
  prime_of_lucasCheck (a := 21) (fs := [(2, 4), (3, 1), (13, 1), (67, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_13 (all_primes_cons sp_67 all_primes_nil))))

private lemma pr_265 : Nat.Prime 2257687 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 3), (41809, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_264 all_primes_nil)))

private lemma pr_266 : Nat.Prime 15632224789 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (577, 1), (2257687, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_577 (all_primes_cons pr_265 all_primes_nil))))

private lemma pr_267 : Nat.Prime 62528899157 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (15632224789, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_266 all_primes_nil))

private lemma pr_268 : Nat.Prime 1427 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (23, 1), (31, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_23 (all_primes_cons sp_31 all_primes_nil)))

private lemma pr_269 : Nat.Prime 1823 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (911, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_911 all_primes_nil))

private lemma pr_270 : Nat.Prime 2753 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 6), (43, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_43 all_primes_nil))

private lemma pr_271 : Nat.Prime 14438011418209 :=
  prime_of_lucasCheck (a := 13) (fs := [(2, 5), (3, 2), (7, 1), (1427, 1), (1823, 1), (2753, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons pr_268 (all_primes_cons pr_269 (all_primes_cons pr_270 all_primes_nil))))))

private lemma pr_272 : Nat.Prime 32500546559884984123793269 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 2), (62528899157, 1), (14438011418209, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_267 (all_primes_cons pr_271 all_primes_nil))))

private lemma pr_273 : Nat.Prime 1229 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (307, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_307 all_primes_nil))

private lemma pr_274 : Nat.Prime 2459 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (1229, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_273 all_primes_nil))

private lemma pr_275 : Nat.Prime 4919 :=
  prime_of_lucasCheck (a := 13) (fs := [(2, 1), (2459, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_274 all_primes_nil))

private lemma pr_276 : Nat.Prime 20038453 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 2), (3, 1), (7, 2), (53, 1), (643, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_53 (all_primes_cons sp_643 all_primes_nil)))))

private lemma pr_277 : Nat.Prime 40099 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (41, 1), (163, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_41 (all_primes_cons sp_163 all_primes_nil))))

private lemma pr_278 : Nat.Prime 64301 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (5, 2), (643, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_643 all_primes_nil)))

private lemma pr_279 : Nat.Prime 46411304383 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 2), (40099, 1), (64301, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_277 (all_primes_cons pr_278 all_primes_nil))))

private lemma pr_280 : Nat.Prime 34667249663877316398712819 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 2), (421, 1), (4919, 1), (20038453, 1), (46411304383, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_421 (all_primes_cons pr_275 (all_primes_cons pr_276 (all_primes_cons pr_279 all_primes_nil))))))

private lemma pr_281 : Nat.Prime 9901 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 2), (5, 2), (11, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_11 all_primes_nil))))

private lemma pr_282 : Nat.Prime 59407 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (9901, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_281 all_primes_nil)))

private lemma pr_283 : Nat.Prime 59169373 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (83, 1), (59407, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_83 (all_primes_cons pr_282 all_primes_nil))))

private lemma pr_284 : Nat.Prime 28637976533 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (11, 2), (59169373, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_283 all_primes_nil)))

private lemma pr_285 : Nat.Prime 1171 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 2), (5, 1), (13, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_13 all_primes_nil))))

private lemma pr_286 : Nat.Prime 7027 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (1171, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_285 all_primes_nil)))

private lemma pr_287 : Nat.Prime 9007 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (19, 1), (79, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_19 (all_primes_cons sp_79 all_primes_nil))))

private lemma pr_288 : Nat.Prime 90071 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (5, 1), (9007, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons pr_287 all_primes_nil)))

private lemma pr_289 : Nat.Prime 3797573503 :=
  prime_of_lucasCheck (a := 17) (fs := [(2, 1), (3, 1), (7027, 1), (90071, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_286 (all_primes_cons pr_288 all_primes_nil))))

private lemma pr_290 : Nat.Prime 2977297626353 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (7, 2), (3797573503, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons pr_289 all_primes_nil)))

private lemma pr_291 : Nat.Prime 36833952767869648673632369 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 4), (3, 3), (28637976533, 1), (2977297626353, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_284 (all_primes_cons pr_290 all_primes_nil))))

private lemma pr_292 : Nat.Prime 3643 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (607, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_607 all_primes_nil)))

private lemma pr_293 : Nat.Prime 79601 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (5, 2), (199, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_199 all_primes_nil)))

private lemma pr_294 : Nat.Prime 2388031 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (3, 1), (5, 1), (79601, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons pr_293 all_primes_nil))))

private lemma pr_295 : Nat.Prime 32423 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (13, 1), (29, 1), (43, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_13 (all_primes_cons sp_29 (all_primes_cons sp_43 all_primes_nil))))

private lemma pr_296 : Nat.Prime 67219 :=
  prime_of_lucasCheck (a := 11) (fs := [(2, 1), (3, 1), (17, 1), (659, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_17 (all_primes_cons sp_659 all_primes_nil))))

private lemma pr_297 : Nat.Prime 13076649823 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (3, 1), (32423, 1), (67219, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_295 (all_primes_cons pr_296 all_primes_nil))))

private lemma pr_298 : Nat.Prime 2798403062123 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (107, 1), (13076649823, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_107 (all_primes_cons pr_297 all_primes_nil)))

private lemma pr_299 : Nat.Prime 39000655871861980948551919 :=
  prime_of_lucasCheck (a := 15) (fs := [(2, 1), (3, 2), (89, 1), (3643, 1), (2388031, 1), (2798403062123, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_89 (all_primes_cons pr_292 (all_primes_cons pr_294 (all_primes_cons pr_298 all_primes_nil))))))

private lemma pr_300 : Nat.Prime 3319 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (3, 1), (7, 1), (79, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_79 all_primes_nil))))

private lemma pr_301 : Nat.Prime 3347 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (7, 1), (239, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_239 all_primes_nil)))

private lemma pr_302 : Nat.Prime 3697 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 4), (3, 1), (7, 1), (11, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_11 all_primes_nil))))

private lemma pr_303 : Nat.Prime 1637 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (409, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_409 all_primes_nil))

private lemma pr_304 : Nat.Prime 51043 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (47, 1), (181, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_47 (all_primes_cons sp_181 all_primes_nil))))

private lemma pr_305 : Nat.Prime 36598137259 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (73, 1), (1637, 1), (51043, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_73 (all_primes_cons pr_303 (all_primes_cons pr_304 all_primes_nil)))))

private lemma pr_306 : Nat.Prime 35134211768641 :=
  prime_of_lucasCheck (a := 17) (fs := [(2, 6), (3, 1), (5, 1), (36598137259, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons pr_305 all_primes_nil))))

private lemma pr_307 : Nat.Prime 1301514969413889898982113823 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (41, 1), (3319, 1), (3347, 1), (3697, 1), (35134211768641, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_41 (all_primes_cons pr_300 (all_primes_cons pr_301 (all_primes_cons pr_302 (all_primes_cons pr_306 all_primes_nil)))))))

private lemma pr_308 : Nat.Prime 4969 :=
  prime_of_lucasCheck (a := 11) (fs := [(2, 3), (3, 3), (23, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_23 all_primes_nil)))

private lemma pr_309 : Nat.Prime 10169 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (31, 1), (41, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_31 (all_primes_cons sp_41 all_primes_nil)))

private lemma pr_310 : Nat.Prime 203381 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (5, 1), (10169, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons pr_309 all_primes_nil)))

private lemma pr_311 : Nat.Prime 5647 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (941, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_941 all_primes_nil)))

private lemma pr_312 : Nat.Prime 34322467 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (1013, 1), (5647, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_134 (all_primes_cons pr_311 all_primes_nil))))

private lemma pr_313 : Nat.Prime 27810462041133169 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 4), (3, 1), (83, 1), (203381, 1), (34322467, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_83 (all_primes_cons pr_310 (all_primes_cons pr_312 all_primes_nil)))))

private lemma pr_314 : Nat.Prime 2211042974118251468177 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 4), (4969, 1), (27810462041133169, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_308 (all_primes_cons pr_313 all_primes_nil)))

private lemma pr_315 : Nat.Prime 2603029938827779797964227623 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (59, 1), (907, 1), (2211042974118251468177, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_59 (all_primes_cons sp_907 (all_primes_cons pr_314 all_primes_nil)))))

private lemma pr_316 : Nat.Prime 1543 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (3, 1), (257, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_257 all_primes_nil)))

private lemma pr_317 : Nat.Prime 7867 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 2), (19, 1), (23, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_19 (all_primes_cons sp_23 all_primes_nil))))

private lemma pr_318 : Nat.Prime 414049 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 5), (3, 1), (19, 1), (227, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_19 (all_primes_cons sp_227 all_primes_nil))))

private lemma pr_319 : Nat.Prime 232695539 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (281, 1), (414049, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_281 (all_primes_cons pr_318 all_primes_nil)))

private lemma pr_320 : Nat.Prime 1051 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (3, 1), (5, 2), (7, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_7 all_primes_nil))))

private lemma pr_321 : Nat.Prime 173570549 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (19, 1), (41, 1), (53, 1), (1051, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_19 (all_primes_cons sp_41 (all_primes_cons sp_53 (all_primes_cons pr_320 all_primes_nil)))))

private lemma pr_322 : Nat.Prime 62832538739 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (181, 1), (173570549, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_181 (all_primes_cons pr_321 all_primes_nil)))

private lemma pr_323 : Nat.Prime 3904544908241669696946341423 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (1543, 1), (7867, 1), (232695539, 1), (62832538739, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_316 (all_primes_cons pr_317 (all_primes_cons pr_319 (all_primes_cons pr_322 all_primes_nil))))))

private lemma pr_324 : Nat.Prime 80513 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 7), (17, 1), (37, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_17 (all_primes_cons sp_37 all_primes_nil)))

private lemma pr_325 : Nat.Prime 535169 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 7), (37, 1), (113, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_37 (all_primes_cons sp_113 all_primes_nil)))

private lemma pr_326 : Nat.Prime 1070339 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (535169, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_325 all_primes_nil))

private lemma pr_327 : Nat.Prime 19266103 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 2), (1070339, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_326 all_primes_nil)))

private lemma pr_328 : Nat.Prime 4159 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 3), (7, 1), (11, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_11 all_primes_nil))))

private lemma pr_329 : Nat.Prime 6632828298433 :=
  prime_of_lucasCheck (a := 11) (fs := [(2, 6), (3, 2), (7, 1), (17, 1), (53, 1), (439, 1), (4159, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_17 (all_primes_cons sp_53 (all_primes_cons sp_439 (all_primes_cons pr_328 all_primes_nil)))))))

private lemma pr_330 : Nat.Prime 5206059877655559595928455223 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (11, 1), (23, 1), (80513, 1), (19266103, 1), (6632828298433, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_23 (all_primes_cons pr_324 (all_primes_cons pr_327 (all_primes_cons pr_329 all_primes_nil))))))

private lemma pr_331 : Nat.Prime 1861 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 1), (31, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_31 all_primes_nil))))

private lemma pr_332 : Nat.Prime 1493 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (373, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_373 all_primes_nil))

private lemma pr_333 : Nat.Prime 1857293 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (311, 1), (1493, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_311 (all_primes_cons pr_332 all_primes_nil)))

private lemma pr_334 : Nat.Prime 26002103 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (7, 1), (1857293, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons pr_333 all_primes_nil)))

private lemma pr_335 : Nat.Prime 780063091 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (5, 1), (26002103, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons pr_334 all_primes_nil))))

private lemma pr_336 : Nat.Prime 28387 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 2), (19, 1), (83, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_19 (all_primes_cons sp_83 all_primes_nil))))

private lemma pr_337 : Nat.Prime 46499 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (67, 1), (347, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_67 (all_primes_cons sp_347 all_primes_nil)))

private lemma pr_338 : Nat.Prime 3041204228353 :=
  prime_of_lucasCheck (a := 10) (fs := [(2, 8), (3, 2), (28387, 1), (46499, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_336 (all_primes_cons pr_337 all_primes_nil))))

private lemma pr_339 : Nat.Prime 6507574847069449494910569023 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (67, 1), (1861, 1), (780063091, 1), (3041204228353, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_67 (all_primes_cons pr_331 (all_primes_cons pr_335 (all_primes_cons pr_338 all_primes_nil))))))

private lemma pr_340 : Nat.Prime 1303 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (3, 1), (7, 1), (31, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_31 all_primes_nil))))

private lemma pr_341 : Nat.Prime 109453 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (7, 1), (1303, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons pr_340 all_primes_nil))))

private lemma pr_342 : Nat.Prime 4576667743 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (3, 2), (23, 1), (101, 1), (109453, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_23 (all_primes_cons sp_101 (all_primes_cons pr_341 all_primes_nil)))))

private lemma pr_343 : Nat.Prime 1069 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 2), (3, 1), (89, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_89 all_primes_nil)))

private lemma pr_344 : Nat.Prime 186007 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (29, 1), (1069, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_29 (all_primes_cons pr_343 all_primes_nil))))

private lemma pr_345 : Nat.Prime 310663 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (3, 3), (11, 1), (523, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons sp_523 all_primes_nil))))

private lemma pr_346 : Nat.Prime 6834587 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (11, 1), (310663, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_345 all_primes_nil)))

private lemma pr_347 : Nat.Prime 2542562048219 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (186007, 1), (6834587, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_344 (all_primes_cons pr_346 all_primes_nil)))

private lemma pr_348 : Nat.Prime 2501881055447497 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 3), (3, 1), (41, 1), (2542562048219, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_41 (all_primes_cons pr_347 all_primes_nil))))

private lemma pr_349 : Nat.Prime 7809089816483339393892682823 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (31, 1), (4576667743, 1), (2501881055447497, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_31 (all_primes_cons pr_342 (all_primes_cons pr_348 all_primes_nil)))))

private lemma pr_350 : Nat.Prime 12421 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 2), (3, 3), (5, 1), (23, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_23 all_primes_nil))))

private lemma pr_351 : Nat.Prime 656321 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 6), (5, 1), (7, 1), (293, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_293 all_primes_nil))))

private lemma pr_352 : Nat.Prime 43317187 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (11, 1), (656321, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons pr_351 all_primes_nil))))

private lemma pr_353 : Nat.Prime 148199617 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 6), (3, 2), (457, 1), (563, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_457 (all_primes_cons sp_563 all_primes_nil))))

private lemma pr_354 : Nat.Prime 2298213407204421683 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (179, 1), (43317187, 1), (148199617, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_179 (all_primes_cons pr_352 (all_primes_cons pr_353 all_primes_nil))))

private lemma pr_355 : Nat.Prime 9110604785897229292874796623 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (89, 1), (163, 1), (12421, 1), (2298213407204421683, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_89 (all_primes_cons sp_163 (all_primes_cons pr_350 (all_primes_cons pr_354 all_primes_nil))))))

private lemma pr_356 : Nat.Prime 66915539 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (127, 1), (463, 1), (569, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_127 (all_primes_cons sp_463 (all_primes_cons sp_569 all_primes_nil))))

private lemma pr_357 : Nat.Prime 4093 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (11, 1), (31, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons sp_31 all_primes_nil))))

private lemma pr_358 : Nat.Prime 25219 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 3), (467, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_467 all_primes_nil)))

private lemma pr_359 : Nat.Prime 10993 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 4), (3, 1), (229, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_229 all_primes_nil)))

private lemma pr_360 : Nat.Prime 43973 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (10993, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_359 all_primes_nil))

private lemma pr_361 : Nat.Prime 7072769311414497659 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (11, 2), (47, 1), (137, 1), (4093, 1), (25219, 1), (43973, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_47 (all_primes_cons sp_137 (all_primes_cons pr_357 (all_primes_cons pr_358 (all_primes_cons pr_360 all_primes_nil)))))))

private lemma pr_362 : Nat.Prime 10412119755311119191856910423 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (66915539, 1), (7072769311414497659, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_356 (all_primes_cons pr_361 all_primes_nil))))

private lemma pr_363 : Nat.Prime 101723 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (181, 1), (281, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_181 (all_primes_cons sp_281 all_primes_nil)))

private lemma pr_364 : Nat.Prime 9437 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (7, 1), (337, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_337 all_primes_nil)))

private lemma pr_365 : Nat.Prime 8682041 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (5, 1), (23, 1), (9437, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_23 (all_primes_cons pr_364 all_primes_nil))))

private lemma pr_366 : Nat.Prime 3348841 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 3), (3, 1), (5, 1), (11, 1), (43, 1), (59, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_11 (all_primes_cons sp_43 (all_primes_cons sp_59 all_primes_nil))))))

private lemma pr_367 : Nat.Prime 190542355219 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 2), (29, 1), (109, 1), (3348841, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_29 (all_primes_cons sp_109 (all_primes_cons pr_366 all_primes_nil)))))

private lemma pr_368 : Nat.Prime 4711840194981902289154877 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (7, 1), (101723, 1), (8682041, 1), (190542355219, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons pr_363 (all_primes_cons pr_365 (all_primes_cons pr_367 all_primes_nil)))))

private lemma pr_369 : Nat.Prime 11713634724725009090839024223 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (113, 1), (4711840194981902289154877, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_113 (all_primes_cons pr_368 all_primes_nil))))

private lemma pr_370 : Nat.Prime 113983 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (11, 2), (157, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_11 (all_primes_cons sp_157 all_primes_nil))))

private lemma pr_371 : Nat.Prime 683899 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (113983, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_370 all_primes_nil)))

private lemma pr_372 : Nat.Prime 9419 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (17, 1), (277, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_17 (all_primes_cons sp_277 all_primes_nil)))

private lemma pr_373 : Nat.Prime 18839 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (9419, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_372 all_primes_nil))

private lemma pr_374 : Nat.Prime 96531037 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (7, 1), (61, 1), (18839, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_61 (all_primes_cons pr_373 all_primes_nil)))))

private lemma pr_375 : Nat.Prime 3833 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (479, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_479 all_primes_nil))

private lemma pr_376 : Nat.Prime 21661 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 1), (19, 2)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_19 all_primes_nil))))

private lemma pr_377 : Nat.Prime 814657126757 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (11, 1), (223, 1), (3833, 1), (21661, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_223 (all_primes_cons pr_375 (all_primes_cons pr_376 all_primes_nil)))))

private lemma pr_378 : Nat.Prime 13015149694138898989821138023 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 2), (683899, 1), (96531037, 1), (814657126757, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_371 (all_primes_cons pr_374 (all_primes_cons pr_377 all_primes_nil)))))

private lemma pr_379 : Nat.Prime 22963 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (43, 1), (89, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_43 (all_primes_cons sp_89 all_primes_nil))))

private lemma pr_380 : Nat.Prime 1544159 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (7, 1), (11, 1), (37, 1), (271, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_11 (all_primes_cons sp_37 (all_primes_cons sp_271 all_primes_nil)))))

private lemma pr_381 : Nat.Prime 77207951 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (5, 2), (1544159, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons pr_380 all_primes_nil)))

private lemma pr_382 : Nat.Prime 154415903 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (77207951, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_381 all_primes_nil))

private lemma pr_383 : Nat.Prime 35515657691 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (23, 1), (154415903, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_23 (all_primes_cons pr_382 all_primes_nil))))

private lemma pr_384 : Nat.Prime 1873 :=
  prime_of_lucasCheck (a := 10) (fs := [(2, 4), (3, 2), (13, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_13 all_primes_nil)))

private lemma pr_385 : Nat.Prime 2441 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 3), (5, 1), (61, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_61 all_primes_nil)))

private lemma pr_386 : Nat.Prime 27431959 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (1873, 1), (2441, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_384 (all_primes_cons pr_385 all_primes_nil))))

private lemma pr_387 : Nat.Prime 199485205849 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 3), (3, 2), (101, 1), (27431959, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_101 (all_primes_cons pr_386 all_primes_nil))))

private lemma pr_388 : Nat.Prime 797940823397 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (199485205849, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_387 all_primes_nil))

private lemma pr_389 : Nat.Prime 14316664663552788888803251823 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (22963, 1), (35515657691, 1), (797940823397, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_379 (all_primes_cons pr_383 (all_primes_cons pr_388 all_primes_nil)))))

private lemma pr_390 : Nat.Prime 1321 :=
  prime_of_lucasCheck (a := 13) (fs := [(2, 3), (3, 1), (5, 1), (11, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_11 all_primes_nil))))

private lemma pr_391 : Nat.Prime 7507 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 3), (139, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_139 all_primes_nil)))

private lemma pr_392 : Nat.Prime 97609 :=
  prime_of_lucasCheck (a := 17) (fs := [(2, 3), (3, 1), (7, 2), (83, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_83 all_primes_nil))))

private lemma pr_393 : Nat.Prime 5679829 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 3), (7, 1), (11, 1), (683, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_11 (all_primes_cons sp_683 all_primes_nil)))))

private lemma pr_394 : Nat.Prime 22805898313626097 :=
  prime_of_lucasCheck (a := 15) (fs := [(2, 4), (3, 1), (857, 1), (97609, 1), (5679829, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_857 (all_primes_cons pr_392 (all_primes_cons pr_393 all_primes_nil)))))

private lemma pr_395 : Nat.Prime 15618179632966678787785365623 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (43, 1), (73, 1), (1321, 1), (7507, 1), (22805898313626097, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_43 (all_primes_cons sp_73 (all_primes_cons pr_390 (all_primes_cons pr_391 (all_primes_cons pr_394 all_primes_nil)))))))

private lemma pr_396 : Nat.Prime 5953 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 6), (3, 1), (31, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_31 all_primes_nil)))

private lemma pr_397 : Nat.Prime 250027 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (7, 1), (5953, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons pr_396 all_primes_nil))))

private lemma pr_398 : Nat.Prime 4523 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (7, 1), (17, 1), (19, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_17 (all_primes_cons sp_19 all_primes_nil))))

private lemma pr_399 : Nat.Prime 108553 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 3), (3, 1), (4523, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_398 all_primes_nil)))

private lemma pr_400 : Nat.Prime 986841762125029 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (211, 1), (991, 1), (3623, 1), (108553, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_211 (all_primes_cons sp_991 (all_primes_cons pr_189 (all_primes_cons pr_399 all_primes_nil))))))

private lemma pr_401 : Nat.Prime 8713812759564006071 :=
  prime_of_lucasCheck (a := 19) (fs := [(2, 1), (5, 1), (883, 1), (986841762125029, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_883 (all_primes_cons pr_400 all_primes_nil))))

private lemma pr_402 : Nat.Prime 16919694602380568686767479423 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (353, 1), (250027, 1), (8713812759564006071, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_353 (all_primes_cons pr_397 (all_primes_cons pr_401 all_primes_nil)))))

private lemma pr_403 : Nat.Prime 2791 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 1), (3, 2), (5, 1), (31, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_31 all_primes_nil))))

private lemma pr_404 : Nat.Prime 9120989 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (19, 1), (43, 1), (2791, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_19 (all_primes_cons sp_43 (all_primes_cons pr_403 all_primes_nil))))

private lemma pr_405 : Nat.Prime 50969 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (23, 1), (277, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_23 (all_primes_cons sp_277 all_primes_nil)))

private lemma pr_406 : Nat.Prime 101939 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (50969, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_405 all_primes_nil))

private lemma pr_407 : Nat.Prime 6067 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 2), (337, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_337 all_primes_nil)))

private lemma pr_408 : Nat.Prime 99668677 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 2), (3, 1), (37, 2), (6067, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_37 (all_primes_cons pr_407 all_primes_nil))))

private lemma pr_409 : Nat.Prime 11720837077847 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (13, 1), (4523, 1), (99668677, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_13 (all_primes_cons pr_398 (all_primes_cons pr_408 all_primes_nil))))

private lemma pr_410 : Nat.Prime 90805591226777045309 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (19, 1), (101939, 1), (11720837077847, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_19 (all_primes_cons pr_406 (all_primes_cons pr_409 all_primes_nil))))

private lemma pr_411 : Nat.Prime 18221209571794458585749593223 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 1), (11, 1), (9120989, 1), (90805591226777045309, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_404 (all_primes_cons pr_410 all_primes_nil))))

private lemma pr_412 : Nat.Prime 5519 :=
  prime_of_lucasCheck (a := 13) (fs := [(2, 1), (31, 1), (89, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_31 (all_primes_cons sp_89 all_primes_nil)))

private lemma pr_413 : Nat.Prime 342179 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (31, 1), (5519, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_31 (all_primes_cons pr_412 all_primes_nil)))

private lemma pr_414 : Nat.Prime 143715181 :=
  prime_of_lucasCheck (a := 14) (fs := [(2, 2), (3, 1), (5, 1), (7, 1), (342179, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons pr_413 all_primes_nil)))))

private lemma pr_415 : Nat.Prime 3011 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (7, 1), (43, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_43 all_primes_nil))))

private lemma pr_416 : Nat.Prime 66033241349 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (89, 1), (3011, 1), (61603, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_89 (all_primes_cons pr_415 (all_primes_cons pr_204 all_primes_nil))))

private lemma pr_417 : Nat.Prime 29054626193561 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 3), (5, 1), (11, 1), (66033241349, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_11 (all_primes_cons pr_416 all_primes_nil))))

private lemma pr_418 : Nat.Prime 6174689158655583721 :=
  prime_of_lucasCheck (a := 58) (fs := [(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (23, 1), (29054626193561, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_11 (all_primes_cons sp_23 (all_primes_cons pr_417 all_primes_nil)))))))

private lemma pr_419 : Nat.Prime 19522724541208348484731707023 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (143715181, 1), (6174689158655583721, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_414 (all_primes_cons pr_418 all_primes_nil))))

private lemma pr_420 : Nat.Prime 2617 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 3), (3, 1), (109, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_109 all_primes_nil)))

private lemma pr_421 : Nat.Prime 258297901 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 1), (5, 2), (7, 1), (47, 1), (2617, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_7 (all_primes_cons sp_47 (all_primes_cons pr_420 all_primes_nil))))))

private lemma pr_422 : Nat.Prime 5711 :=
  prime_of_lucasCheck (a := 19) (fs := [(2, 1), (5, 1), (571, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_571 all_primes_nil)))

private lemma pr_423 : Nat.Prime 80045377 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 6), (3, 1), (73, 1), (5711, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_73 (all_primes_cons pr_422 all_primes_nil))))

private lemma pr_424 : Nat.Prime 320181509 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (80045377, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_423 all_primes_nil))

private lemma pr_425 : Nat.Prime 165404423427425219 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (258297901, 1), (320181509, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_421 (all_primes_cons pr_424 all_primes_nil)))

private lemma pr_426 : Nat.Prime 11404293269782167789547547 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (11, 1), (61, 1), (83, 1), (619, 1), (165404423427425219, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_61 (all_primes_cons sp_83 (all_primes_cons sp_619 (all_primes_cons pr_425 all_primes_nil))))))

private lemma pr_427 : Nat.Prime 20824239510622238383713820823 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (83, 1), (11404293269782167789547547, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_83 (all_primes_cons pr_426 all_primes_nil))))

private lemma pr_428 : Nat.Prime 830257 :=
  prime_of_lucasCheck (a := 10) (fs := [(2, 4), (3, 1), (7, 2), (353, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_353 all_primes_nil))))

private lemma pr_429 : Nat.Prime 7193 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (29, 1), (31, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_29 (all_primes_cons sp_31 all_primes_nil)))

private lemma pr_430 : Nat.Prime 14387 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (7193, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_429 all_primes_nil))

private lemma pr_431 : Nat.Prime 1237283 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (43, 1), (14387, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_43 (all_primes_cons pr_430 all_primes_nil)))

private lemma pr_432 : Nat.Prime 1108605569 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 7), (7, 1), (1237283, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons pr_431 all_primes_nil)))

private lemma pr_433 : Nat.Prime 31729 :=
  prime_of_lucasCheck (a := 7) (fs := [(2, 4), (3, 1), (661, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_661 all_primes_nil)))

private lemma pr_434 : Nat.Prime 2474863 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (13, 1), (31729, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_13 (all_primes_cons pr_433 all_primes_nil))))

private lemma pr_435 : Nat.Prime 534570409 :=
  prime_of_lucasCheck (a := 29) (fs := [(2, 3), (3, 3), (2474863, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_434 all_primes_nil)))

private lemma pr_436 : Nat.Prime 1092661915997 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 2), (7, 1), (73, 1), (534570409, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_73 (all_primes_cons pr_435 all_primes_nil))))

private lemma pr_437 : Nat.Prime 22125754480036128282695934623 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (830257, 1), (1108605569, 1), (1092661915997, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_428 (all_primes_cons pr_432 (all_primes_cons pr_436 all_primes_nil)))))

private lemma pr_438 : Nat.Prime 168029 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (7, 1), (17, 1), (353, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_7 (all_primes_cons sp_17 (all_primes_cons sp_353 all_primes_nil))))

private lemma pr_439 : Nat.Prime 91621 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 2), (3, 2), (5, 1), (509, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_5 (all_primes_cons sp_509 all_primes_nil))))

private lemma pr_440 : Nat.Prime 154839491 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (13, 2), (91621, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_13 (all_primes_cons pr_439 all_primes_nil))))

private lemma pr_441 : Nat.Prime 309678983 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (154839491, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons pr_440 all_primes_nil))

private lemma pr_442 : Nat.Prime 327559 :=
  prime_of_lucasCheck (a := 12) (fs := [(2, 1), (3, 1), (7, 1), (11, 1), (709, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons sp_11 (all_primes_cons sp_709 all_primes_nil)))))

private lemma pr_443 : Nat.Prime 3470891 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (5, 1), (17, 2), (1201, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_5 (all_primes_cons sp_17 (all_primes_cons pr_58 all_primes_nil))))

private lemma pr_444 : Nat.Prime 20464588531243 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 2), (327559, 1), (3470891, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_442 (all_primes_cons pr_443 all_primes_nil))))

private lemma pr_445 : Nat.Prime 23427269449450018181678048423 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (168029, 1), (309678983, 1), (20464588531243, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_438 (all_primes_cons pr_441 (all_primes_cons pr_444 all_primes_nil)))))

private lemma pr_446 : Nat.Prime 1777 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 4), (3, 1), (37, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_37 all_primes_nil)))

private lemma pr_447 : Nat.Prime 9859 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 1), (31, 1), (53, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_31 (all_primes_cons sp_53 all_primes_nil))))

private lemma pr_448 : Nat.Prime 3559 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 1), (3, 1), (593, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_593 all_primes_nil)))

private lemma pr_449 : Nat.Prime 42709 :=
  prime_of_lucasCheck (a := 6) (fs := [(2, 2), (3, 1), (3559, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons pr_448 all_primes_nil)))

private lemma pr_450 : Nat.Prime 2607649843727 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (17, 1), (23, 1), (163, 1), (479, 1), (42709, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_17 (all_primes_cons sp_23 (all_primes_cons sp_163 (all_primes_cons sp_479 (all_primes_cons pr_449 all_primes_nil))))))

private lemma pr_451 : Nat.Prime 22675179071806562827 :=
  prime_of_lucasCheck (a := 2) (fs := [(2, 1), (3, 2), (7, 2), (9859, 1), (2607649843727, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_3 (all_primes_cons sp_7 (all_primes_cons pr_447 (all_primes_cons pr_450 all_primes_nil)))))

private lemma pr_452 : Nat.Prime 3545853802532823068634953 :=
  prime_of_lucasCheck (a := 3) (fs := [(2, 3), (11, 1), (1777, 1), (22675179071806562827, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons pr_446 (all_primes_cons pr_451 all_primes_nil))))

private lemma pr_453 : Nat.Prime 24728784418863908080660162223 :=
  prime_of_lucasCheck (a := 5) (fs := [(2, 1), (11, 1), (317, 1), (3545853802532823068634953, 1)]) (by decide +kernel) (all_primes_cons sp_2 (all_primes_cons sp_11 (all_primes_cons sp_317 (all_primes_cons pr_452 all_primes_nil))))

private lemma ap_2 : OeisA7918.isApOfNPrimes 2 2 1 := by
  refine ⟨by decide, fun k hk => ?_⟩
  interval_cases k
  · exact sp_2
  · exact sp_3

private lemma ap_3 : OeisA7918.isApOfNPrimes 3 3 2 := by
  refine ⟨by decide, fun k hk => ?_⟩
  interval_cases k
  · exact sp_3
  · exact sp_5
  · exact sp_7

private lemma ap_5 : OeisA7918.isApOfNPrimes 5 5 6 := by
  refine ⟨by decide, fun k hk => ?_⟩
  interval_cases k
  · exact sp_5
  · exact sp_11
  · exact sp_17
  · exact sp_23
  · exact sp_29

private lemma ap_7 : OeisA7918.isApOfNPrimes 7 7 150 := by
  refine ⟨by decide, fun k hk => ?_⟩
  interval_cases k
  · exact sp_7
  · exact sp_157
  · exact sp_307
  · exact sp_457
  · exact sp_607
  · exact sp_757
  · exact sp_907

private lemma ap_11 : OeisA7918.isApOfNPrimes 11 11 1536160080 := by
  refine ⟨by decide, fun k hk => ?_⟩
  interval_cases k
  · exact sp_11
  · exact pr_3
  · exact pr_5
  · exact pr_7
  · exact pr_8
  · exact pr_12
  · exact pr_15
  · exact pr_18
  · exact pr_21
  · exact pr_23
  · exact pr_25

private lemma ap_13 : OeisA7918.isApOfNPrimes 13 13 9918821194590 := by
  refine ⟨by decide, fun k hk => ?_⟩
  interval_cases k
  · exact sp_13
  · exact pr_30
  · exact pr_31
  · exact pr_34
  · exact pr_39
  · exact pr_43
  · exact pr_45
  · exact pr_48
  · exact pr_51
  · exact pr_54
  · exact pr_57
  · exact pr_61
  · exact pr_65

private lemma ap_17 : OeisA7918.isApOfNPrimes 17 17 341976204789992332560 := by
  refine ⟨by decide, fun k hk => ?_⟩
  interval_cases k
  · exact sp_17
  · exact pr_71
  · exact pr_77
  · exact pr_82
  · exact pr_86
  · exact pr_91
  · exact pr_95
  · exact pr_103
  · exact pr_108
  · exact pr_114
  · exact pr_120
  · exact pr_126
  · exact pr_132
  · exact pr_139
  · exact pr_145
  · exact pr_151
  · exact pr_157

private lemma ap_19 : OeisA7918.isApOfNPrimes 19 19 2166703103992332274919550 := by
  refine ⟨by decide, fun k hk => ?_⟩
  interval_cases k
  · exact sp_19
  · exact pr_162
  · exact pr_171
  · exact pr_177
  · exact pr_187
  · exact pr_193
  · exact pr_202
  · exact pr_210
  · exact pr_220
  · exact pr_228
  · exact pr_237
  · exact pr_243
  · exact pr_250
  · exact pr_257
  · exact pr_263
  · exact pr_272
  · exact pr_280
  · exact pr_291
  · exact pr_299

private lemma ap_20 : OeisA7918.isApOfNPrimes 20 23 1301514969413889898982113800 := by
  refine ⟨by decide, fun k hk => ?_⟩
  interval_cases k
  · exact sp_23
  · exact pr_307
  · exact pr_315
  · exact pr_323
  · exact pr_330
  · exact pr_339
  · exact pr_349
  · exact pr_355
  · exact pr_362
  · exact pr_369
  · exact pr_378
  · exact pr_389
  · exact pr_395
  · exact pr_402
  · exact pr_411
  · exact pr_419
  · exact pr_427
  · exact pr_437
  · exact pr_445
  · exact pr_453

private lemma ap_mono {n m p0 d : ℕ} (hnm : n ≤ m) (h : OeisA7918.isApOfNPrimes m p0 d) :
    OeisA7918.isApOfNPrimes n p0 d :=
  ⟨h.1, fun k hk => h.2 k (lt_of_lt_of_le hk hnm)⟩

private lemma a_eq_of_isLeast {n p : ℕ} (hp : p.Prime) (hnp : n ≤ p)
    (hmin : ∀ m : ℕ, n ≤ m → m < p → ¬ m.Prime) : OeisA7918.a n = p := by
  unfold OeisA7918.a
  have hleast : IsLeast {q : ℕ | q.Prime ∧ n ≤ q} p := by
    refine ⟨⟨hp, hnp⟩, fun q hq => ?_⟩
    by_contra hlt
    exact hmin q hq.2 (lt_of_not_ge hlt) hq.1
  exact hleast.csInf_eq

private lemma a_eq_check (n p : ℕ)
    (h : isPrimeSmall p && decide (n ≤ p) &&
      (List.range p).all (fun m => decide (m < n) || !isPrimeSmall m) = true) :
    OeisA7918.a n = p := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨hp, hnp⟩, hmin⟩ := h
  have hp1000 : p ≤ 1000 := by
    simp only [isPrimeSmall, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.1.2
  refine a_eq_of_isLeast (prime_of_isPrimeSmall hp) hnp fun m hnm hmp hmp_prime => ?_
  have hchk := hmin m (List.mem_range.mpr hmp)
  rcases hchk with hlt | hnf
  · omega
  · have htrue : isPrimeSmall m = true := by
      simp only [isPrimeSmall, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨hmp_prime.two_le, by omega⟩, ?_⟩
      suffices ∀ k : ℕ, (∀ d : ℕ, 2 ≤ d → d ≤ k → ¬ (d ∣ m)) → hasNoDivisorUpTo m k = true from
        this (min 32 (m - 1)) fun d hd2 hdk hdvd => by
          rcases (Nat.dvd_prime hmp_prime).mp hdvd with h1 | hdm <;> omega
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        cases k with
        | zero => rfl
        | succ r =>
          simp only [hasNoDivisorUpTo, Bool.and_eq_true, bne_iff_ne, ne_eq]
          refine ⟨fun hmod => hk (r + 2) (by omega) le_rfl (Nat.dvd_of_mod_eq_zero hmod),
            ih fun d hd2 hdr => hk d hd2 (by omega)⟩
    rw [htrue] at hnf
    exact Bool.false_ne_true hnf.symm

end OeisA7918R2H1

theorem OMA.solution : OMA.R_OeisA7918_conjecture1_R2.H1 := by
  intro n hn1 hn20
  interval_cases n
  · rw [OeisA7918R2H1.a_eq_check 1 2 (by decide)]; exact ⟨1, OeisA7918R2H1.ap_mono (by decide) OeisA7918R2H1.ap_2⟩
  · rw [OeisA7918R2H1.a_eq_check 2 2 (by decide)]; exact ⟨1, OeisA7918R2H1.ap_2⟩
  · rw [OeisA7918R2H1.a_eq_check 3 3 (by decide)]; exact ⟨2, OeisA7918R2H1.ap_3⟩
  · rw [OeisA7918R2H1.a_eq_check 4 5 (by decide)]; exact ⟨6, OeisA7918R2H1.ap_mono (by decide) OeisA7918R2H1.ap_5⟩
  · rw [OeisA7918R2H1.a_eq_check 5 5 (by decide)]; exact ⟨6, OeisA7918R2H1.ap_5⟩
  · rw [OeisA7918R2H1.a_eq_check 6 7 (by decide)]; exact ⟨150, OeisA7918R2H1.ap_mono (by decide) OeisA7918R2H1.ap_7⟩
  · rw [OeisA7918R2H1.a_eq_check 7 7 (by decide)]; exact ⟨150, OeisA7918R2H1.ap_7⟩
  · rw [OeisA7918R2H1.a_eq_check 8 11 (by decide)]; exact ⟨1536160080, OeisA7918R2H1.ap_mono (by decide) OeisA7918R2H1.ap_11⟩
  · rw [OeisA7918R2H1.a_eq_check 9 11 (by decide)]; exact ⟨1536160080, OeisA7918R2H1.ap_mono (by decide) OeisA7918R2H1.ap_11⟩
  · rw [OeisA7918R2H1.a_eq_check 10 11 (by decide)]; exact ⟨1536160080, OeisA7918R2H1.ap_mono (by decide) OeisA7918R2H1.ap_11⟩
  · rw [OeisA7918R2H1.a_eq_check 11 11 (by decide)]; exact ⟨1536160080, OeisA7918R2H1.ap_11⟩
  · rw [OeisA7918R2H1.a_eq_check 12 13 (by decide)]; exact ⟨9918821194590, OeisA7918R2H1.ap_mono (by decide) OeisA7918R2H1.ap_13⟩
  · rw [OeisA7918R2H1.a_eq_check 13 13 (by decide)]; exact ⟨9918821194590, OeisA7918R2H1.ap_13⟩
  · rw [OeisA7918R2H1.a_eq_check 14 17 (by decide)]; exact ⟨341976204789992332560, OeisA7918R2H1.ap_mono (by decide) OeisA7918R2H1.ap_17⟩
  · rw [OeisA7918R2H1.a_eq_check 15 17 (by decide)]; exact ⟨341976204789992332560, OeisA7918R2H1.ap_mono (by decide) OeisA7918R2H1.ap_17⟩
  · rw [OeisA7918R2H1.a_eq_check 16 17 (by decide)]; exact ⟨341976204789992332560, OeisA7918R2H1.ap_mono (by decide) OeisA7918R2H1.ap_17⟩
  · rw [OeisA7918R2H1.a_eq_check 17 17 (by decide)]; exact ⟨341976204789992332560, OeisA7918R2H1.ap_17⟩
  · rw [OeisA7918R2H1.a_eq_check 18 19 (by decide)]; exact ⟨2166703103992332274919550, OeisA7918R2H1.ap_mono (by decide) OeisA7918R2H1.ap_19⟩
  · rw [OeisA7918R2H1.a_eq_check 19 19 (by decide)]; exact ⟨2166703103992332274919550, OeisA7918R2H1.ap_19⟩
  · rw [OeisA7918R2H1.a_eq_check 20 23 (by decide)]; exact ⟨1301514969413889898982113800, OeisA7918R2H1.ap_20⟩
