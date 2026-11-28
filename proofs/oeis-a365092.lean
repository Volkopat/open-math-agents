import OMAStatements.S_oeis_a365092
import Mathlib

namespace OMA.A365092Proof

open OMA.S_oeis_a365092

/-! ## The closed form `G` of A001144 and its growth -/

/-- Closed form of A001144: `1, 2, 3, 4, 9, 27` for `n = 1, ..., 6`, then `G (n + 7) = 2 ^ G (n + 5)`. -/
def G : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 9
  | 6 => 27
  | n + 7 => 2 ^ G (n + 5)

theorem G_rec (n : ℕ) (h : 7 ≤ n) : G n = 2 ^ G (n - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 2 = m + 5 by omega]
  rfl

theorem G_succ : ∀ n, G n + 1 ≤ G (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 7 with h | h
    · interval_cases n <;> decide
    · rw [G_rec n h, G_rec (n + 1) (by omega), show n + 1 - 2 = n - 2 + 1 by omega]
      have h1 := Nat.pow_le_pow_right (show 2 > 0 by norm_num) (ih (n - 2) (by omega))
      rw [Nat.pow_succ] at h1
      have h2 : 0 < 2 ^ G (n - 2) := by positivity
      omega

theorem G_mono {m n : ℕ} (h : m ≤ n) : G m ≤ G n :=
  monotone_nat_of_le_succ (fun k => le_trans (Nat.le_succ _) (G_succ k)) h

theorem G_ge : ∀ n, n ≤ G n
  | 0 => Nat.zero_le _
  | n + 1 => le_trans (Nat.add_le_add_right (G_ge n) 1) (G_succ n)

theorem G_two_le {x : ℕ} (h : 2 ≤ G x) : 2 ≤ x := by
  by_contra hx
  have h1 : G x ≤ G 1 := G_mono (by omega)
  have h2 : G 1 = 1 := rfl
  omega

theorem G_nine : 2 ^ 64 ≤ G 9 := by
  have h7 : G 7 = 512 := by decide
  rw [G_rec 9 (by norm_num), show 9 - 2 = 7 from rfl, h7]
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

theorem G_big {x n : ℕ} (hx : x ≤ 2 ^ 64) (hn : 9 ≤ n) : x ≤ G n :=
  le_trans hx (le_trans G_nine (G_mono hn))

theorem G_two_pow (n : ℕ) : 2 ^ G n ≤ G (n + 2) := by
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> decide
  · have e : G (n + 2) = 2 ^ G n := by
      rw [G_rec (n + 2) (by omega), show n + 2 - 2 = n by omega]
    exact e.ge

theorem G_double (n : ℕ) (hn : 4 ≤ n) : 2 * G n ≤ G (n + 1) := by
  rcases Nat.lt_or_ge n 7 with h | h
  · interval_cases n <;> decide
  · rw [G_rec n h, G_rec (n + 1) (by omega), show n + 1 - 2 = n - 2 + 1 by omega]
    have h1 := Nat.pow_le_pow_right (show 2 > 0 by norm_num) (G_succ (n - 2))
    rw [Nat.pow_succ] at h1
    omega

theorem G_eight (n : ℕ) (hn : 6 ≤ n) : 8 * G n ≤ G (n + 1) := by
  rcases Nat.lt_or_ge n 7 with h | h
  · interval_cases n <;> decide
  · rw [G_rec n h, G_rec (n + 1) (by omega), show n + 1 - 2 = n - 2 + 1 by omega]
    have h1 := G_double (n - 2) (by omega)
    have h2 := G_ge (n - 2)
    have h3 : G (n - 2) + 3 ≤ G (n - 2 + 1) := by omega
    have h4 := Nat.pow_le_pow_right (show 2 > 0 by norm_num) h3
    rw [Nat.pow_add, show (2 : ℕ) ^ 3 = 8 by norm_num] at h4
    omega

theorem natMulLePow (x y : ℕ) (hx : 2 ≤ x) (hy : 1 ≤ y) : x * y ≤ x ^ y := by
  induction y with
  | zero => omega
  | succ y ih =>
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · subst h0
      simp
    · have ih' := ih h0
      have h1 : x ≤ x ^ y := by
        calc x = x ^ 1 := (pow_one x).symm
          _ ≤ x ^ y := Nat.pow_le_pow_right (by omega) h0
      have h2 : 2 * x ^ y ≤ x * x ^ y := Nat.mul_le_mul hx (le_refl _)
      have h3 : x ^ y * x = x * x ^ y := Nat.mul_comm _ _
      rw [Nat.pow_succ, mul_add, mul_one]
      omega

/-- The key inequality: `G a ^ G b ≤ G (a + b)` for `a, b ≥ 2`. -/
theorem G_pow : ∀ a b, 2 ≤ a → 2 ≤ b → G a ^ G b ≤ G (a + b) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b ha hb
    rcases Nat.lt_or_ge a 7 with h7 | h7
    · rcases Nat.lt_or_ge b 6 with hb6 | hb6
      · interval_cases a <;> interval_cases b <;>
          first | exact G_big (by decide) (by omega) | decide
      · rcases Nat.eq_or_lt_of_le ha with h2 | h3
        · subst h2
          have e : G 2 = 2 := rfl
          rw [e, Nat.add_comm]
          exact G_two_pow b
        · have hGa : G a ≤ 32 := le_trans (G_mono (show a ≤ 6 by omega)) (by decide)
          have e1 : G (a + b) = 2 ^ G (a + b - 2) := G_rec (a + b) (by omega)
          have h8 := G_eight b hb6
          have hm : G (b + 1) ≤ G (a + b - 2) := G_mono (by omega)
          calc G a ^ G b ≤ 32 ^ G b := Nat.pow_le_pow_left hGa _
            _ = (2 ^ 5) ^ G b := rfl
            _ = 2 ^ (5 * G b) := (Nat.pow_mul 2 5 (G b)).symm
            _ ≤ 2 ^ G (a + b - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = G (a + b) := e1.symm
    · have e1 : G a = 2 ^ G (a - 2) := G_rec a h7
      have e2 : G (a + b) = 2 ^ G (a + b - 2) := G_rec (a + b) (by omega)
      have ih' := ih (a - 2) (by omega) b (by omega) hb
      have hGa2 : 2 ≤ G (a - 2) := le_trans (by omega) (G_ge (a - 2))
      have hGb : 1 ≤ G b := le_trans (by omega) (G_ge b)
      have hmul := natMulLePow (G (a - 2)) (G b) hGa2 hGb
      rw [show a - 2 + b = a + b - 2 by omega] at ih'
      rw [e1, e2, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (le_trans hmul ih')

theorem G_mul (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) : G a * G b ≤ G (a + b) :=
  le_trans (natMulLePow _ _ (le_trans ha (G_ge a)) (le_trans (by omega) (G_ge b))) (G_pow a b ha hb)

/-! ## `A001144 k = G k` -/

theorem pow_G_le (x s : ℕ) (hx : 0 < x) (hs : 1 ≤ s) : x ^ G s ≤ G (x + s) := by
  rcases Nat.lt_or_ge x 2 with h | h
  · have hx1 : x = 1 := by omega
    subst hx1
    rw [one_pow]
    have := G_ge (1 + s)
    omega
  · rcases Nat.lt_or_ge s 2 with h' | h'
    · have hs1 : s = 1 := by omega
      subst hs1
      have hG1 : G 1 = 1 := rfl
      rw [hG1, pow_one]
      have := G_ge (x + 1)
      omega
    · calc x ^ G s ≤ G x ^ G s := Nat.pow_le_pow_left (G_ge x) _
        _ ≤ G (x + s) := G_pow x s h h'

theorem tower_le : ∀ l : List ℕ, (∀ x ∈ l, 0 < x) → l ≠ [] → tower l ≤ G l.sum
  | [], _, h => absurd rfl h
  | [x], _, _ => by
      show x ^ 1 ≤ G (x + 0)
      rw [pow_one, add_zero]
      exact G_ge x
  | x :: y :: l, hpos, _ => by
      have hx : 0 < x := hpos x (List.mem_cons.2 (Or.inl rfl))
      have hy : 0 < y := hpos y (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
      have ih := tower_le (y :: l) (fun z hz => hpos z (List.mem_cons.2 (Or.inr hz))) (by simp)
      have hs : 1 ≤ (y :: l).sum := by
        show 1 ≤ y + l.sum
        omega
      show x ^ tower (y :: l) ≤ G (x + (y :: l).sum)
      calc x ^ tower (y :: l) ≤ x ^ G (y :: l).sum := Nat.pow_le_pow_right hx ih
        _ ≤ G (x + (y :: l).sum) := pow_G_le x _ hx hs

/-- A composition of `k` whose tower value is `G k`. -/
def wit : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [2]
  | 3 => [3]
  | 4 => [4]
  | 5 => [3, 2]
  | 6 => [3, 3]
  | n + 7 => 2 :: wit (n + 5)

theorem wit_spec : ∀ k, 1 ≤ k → (wit k).sum = k ∧ (∀ x ∈ wit k, 0 < x) ∧ tower (wit k) = G k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 7 with h7 | h7
    · interval_cases k <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
      obtain ⟨h1, h2, h3⟩ := ih (m + 5) (by omega) (by omega)
      have ew : wit (m + 7) = 2 :: wit (m + 5) := rfl
      have eG : G (m + 7) = 2 ^ G (m + 5) := rfl
      rw [ew, eG]
      refine ⟨?_, ?_, ?_⟩
      · show 2 + (wit (m + 5)).sum = m + 7
        omega
      · intro x hx
        rcases List.mem_cons.1 hx with h | h
        · omega
        · exact h2 x h
      · show 2 ^ tower (wit (m + 5)) = 2 ^ G (m + 5)
        rw [h3]

theorem A001144_eq (k : ℕ) (hk : 1 ≤ k) : A001144 k = G k := by
  apply le_antisymm
  · show Finset.univ.sup (fun c : Composition k => tower c.blocks) ≤ G k
    apply Finset.sup_le
    intro c _
    have hne : c.blocks ≠ [] := by
      intro h
      have hs := c.blocks_sum
      rw [h, List.sum_nil] at hs
      omega
    have := tower_le c.blocks (fun x hx => c.blocks_pos hx) hne
    rwa [c.blocks_sum] at this
  · obtain ⟨h1, h2, h3⟩ := wit_spec k hk
    have hle := Finset.le_sup (f := fun c : Composition k => tower c.blocks)
      (Finset.mem_univ (⟨wit k, fun hi => h2 _ hi, h1⟩ : Composition k))
    rw [← h3]
    exact hle

/-! ## Facts about `A365092` -/

theorem f_le_one {n : ℕ} (h : n ≤ 1) : A365092 n = 0 := by
  rw [A365092, dif_pos h]

theorem f_two : A365092 2 = 2 := by
  rw [A365092]
  split_ifs <;> omega

theorem f_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : A365092 p = A365092 (p - 1) + 1 := by
  have h3 := hp.two_le
  conv_lhs => rw [A365092]
  split_ifs <;>
    omega

theorem f_composite {n : ℕ} (h2 : 2 ≤ n) (hp : ¬ n.Prime) :
    A365092 n = ∑ q ∈ n.primeFactors, (A365092 q + A365092 (n.factorization q)) := by
  conv_lhs => rw [A365092]
  split_ifs <;>
    first
    | omega
    | exact absurd ‹Nat.Prime n› hp
    | exact absurd (show Nat.Prime n by rw [‹n = 2›]; exact Nat.prime_two) hp
    | exact Finset.sum_attach n.primeFactors (fun q => A365092 q + A365092 (n.factorization q))

theorem f_sum (n : ℕ) (hn : n ≠ 0) :
    A365092 n = ∑ p ∈ n.primeFactors, (A365092 p + A365092 (n.factorization p)) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    rw [Nat.primeFactors_one, Finset.sum_empty, f_le_one (le_refl 1)]
  · by_cases hp : n.Prime
    · rw [hp.primeFactors, Finset.sum_singleton, hp.factorization_self, f_le_one (le_refl 1),
        add_zero]
    · exact f_composite h hp

theorem f_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hc : Nat.Coprime m n) :
    A365092 (m * n) = A365092 m + A365092 n := by
  rw [f_sum (m * n) (mul_ne_zero hm hn), Nat.Coprime.primeFactors_mul hc,
    Finset.sum_union hc.disjoint_primeFactors, f_sum m hm, f_sum n hn]
  congr 1
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hnd : ¬ p ∣ n := (Nat.Prime.coprime_iff_not_dvd hpp).1
      (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hc)
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hnd,
      add_zero]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hmd : ¬ p ∣ m := (Nat.Prime.coprime_iff_not_dvd hpp).1
      (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hc.symm)
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hmd,
      zero_add]

theorem f_pow (p e : ℕ) (hp : p.Prime) (he : e ≠ 0) : A365092 (p ^ e) = A365092 p + A365092 e := by
  rw [f_sum (p ^ e) (pow_ne_zero e hp.ne_zero), Nat.primeFactors_prime_pow he hp, Finset.sum_singleton,
    hp.factorization_pow, Finsupp.single_eq_same]

theorem f_three : A365092 3 = 3 := by
  rw [f_prime Nat.prime_three (by norm_num)]
  have := f_two
  show A365092 2 + 1 = 3
  omega

/-- `a (G k) = k` for `k ≥ 2`. -/
theorem f_G : ∀ k, 2 ≤ k → A365092 (G k) = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have h2 := f_two
    have h3 := f_three
    rcases Nat.lt_or_ge k 7 with h7 | h7
    · interval_cases k
      · exact h2
      · exact h3
      · show A365092 (2 ^ 2) = 4
        rw [f_pow 2 2 Nat.prime_two (by norm_num)]
        omega
      · show A365092 (3 ^ 2) = 5
        rw [f_pow 3 2 Nat.prime_three (by norm_num)]
        omega
      · show A365092 (3 ^ 3) = 6
        rw [f_pow 3 3 Nat.prime_three (by norm_num)]
        omega
    · rw [G_rec k h7, f_pow 2 (G (k - 2)) Nat.prime_two (by have := G_ge (k - 2); omega),
        ih (k - 2) (by omega) (by omega)]
      omega

/-- Every `n ≥ 2` is at most `G (a n)`. -/
theorem f_bound : ∀ n, 2 ≤ n → n ≤ G (A365092 n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hp : n.Prime
    · by_cases h2 : n = 2
      · subst h2
        rw [f_two]
        decide
      · rw [f_prime hp h2]
        have h1 := ih (n - 1) (by omega) (by have := hp.two_le; omega)
        have h3 := G_succ (A365092 (n - 1))
        omega
    · have hn0 : n ≠ 0 := by omega
      obtain ⟨p, hpdef⟩ : ∃ p, p = n.minFac := ⟨_, rfl⟩
      have hpp : p.Prime := by rw [hpdef]; exact Nat.minFac_prime (by omega)
      have hpdvd : p ∣ n := by rw [hpdef]; exact Nat.minFac_dvd n
      obtain ⟨e, hedef⟩ : ∃ e, e = n.factorization p := ⟨_, rfl⟩
      have he : 1 ≤ e := by rw [hedef]; exact hpp.factorization_pos_of_dvd hn0 hpdvd
      have hen : e < n := by rw [hedef]; exact Nat.factorization_lt p hn0
      obtain ⟨m, hmdef⟩ : ∃ m, m = n / p ^ e := ⟨_, rfl⟩
      have hsplit : p ^ e * m = n := by
        rw [hmdef, hedef]; exact Nat.ordProj_mul_ordCompl_eq_self n p
      have hcop : Nat.Coprime (p ^ e) m := by
        rw [hmdef, hedef]; exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hpp hn0)
      have hpe2 : 2 ≤ p ^ e :=
        le_trans hpp.two_le (le_trans (le_of_eq (pow_one p).symm) (Nat.pow_le_pow_right hpp.pos he))
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hsplit
        omega
      rcases Nat.lt_or_ge m 2 with hm | hm
      · have hm1 : m = 1 := by omega
        rw [hm1, mul_one] at hsplit
        have he2 : 2 ≤ e := by
          by_contra hcon
          have he1 : e = 1 := by omega
          rw [he1, pow_one] at hsplit
          rw [← hsplit] at hp
          exact hp hpp
        have hpn : p < n := by
          rw [← hsplit]
          have h22 := hpp.two_le
          calc p < p ^ 2 := by
                have := Nat.mul_le_mul (le_refl p) h22
                rw [pow_two]
                omega
            _ ≤ p ^ e := Nat.pow_le_pow_right hpp.pos he2
        rw [← hsplit, f_pow p e hpp (by omega)]
        have h1 := ih p hpn hpp.two_le
        have h2 := ih e hen he2
        have ha := G_two_le (le_trans hpp.two_le h1)
        have hb := G_two_le (le_trans he2 h2)
        calc p ^ e ≤ G (A365092 p) ^ e := Nat.pow_le_pow_left h1 e
          _ ≤ G (A365092 p) ^ G (A365092 e) := Nat.pow_le_pow_right (by have := hpp.two_le; omega) h2
          _ ≤ G (A365092 p + A365092 e) := G_pow _ _ ha hb
      · have hlt1 : p ^ e < n := by
          rw [← hsplit]
          have := Nat.mul_le_mul (le_refl (p ^ e)) hm
          omega
        have hlt2 : m < n := by
          rw [← hsplit]
          have := Nat.mul_le_mul hpe2 (le_refl m)
          omega
        rw [← hsplit, f_mul (by omega) hm0 hcop]
        have h1 := ih (p ^ e) hlt1 hpe2
        have h2 := ih m hlt2 hm
        have ha := G_two_le (le_trans hpe2 h1)
        have hb := G_two_le (le_trans hm h2)
        calc p ^ e * m ≤ G (A365092 (p ^ e)) * G (A365092 m) := Nat.mul_le_mul h1 h2
          _ ≤ G (A365092 (p ^ e) + A365092 m) := G_mul _ _ ha hb

end OMA.A365092Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a365092.main := by
  intro k hk
  rw [OMA.A365092Proof.A001144_eq k (by omega)]
  refine ⟨?_, ?_⟩
  · show 1 ≤ OMA.A365092Proof.G k ∧ OMA.S_oeis_a365092.A365092 (OMA.A365092Proof.G k) = k
    exact ⟨le_trans (by omega) (OMA.A365092Proof.G_ge k), OMA.A365092Proof.f_G k hk⟩
  · intro n hn
    have hn' : 1 ≤ n ∧ OMA.S_oeis_a365092.A365092 n = k := hn
    obtain ⟨hn1, hnk⟩ := hn'
    rcases Nat.lt_or_ge n 2 with h | h
    · have h0 := OMA.A365092Proof.f_le_one (show n ≤ 1 by omega)
      omega
    · have hb := OMA.A365092Proof.f_bound n h
      rw [hnk] at hb
      exact hb
