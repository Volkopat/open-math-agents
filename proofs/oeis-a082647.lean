import OMAStatements.S_oeis_a082647

/-!
# A082647: Omar E. Pol's two formula conjectures

Credit: @surrenderyourfreedom

Idea. `n` is a sum of `d` consecutive positive integers with `d ∣ n` iff `d` is odd and
`d^2 < 2n`; `n` is a sum of `2k` consecutive positive integers iff `n = k * o` with `o` odd and
`o^2 > 2n` (`o` = first + last term). So `a(n)` counts the odd divisors below `sqrt(2n)` and
A131576 the odd divisors above it, giving `a(n) = A001227(n) - A131576(n)`.
For the middle divisors write `n = 2^a m` with `m` odd and split the odd divisors `d` into
`B` (`2n < d^2`), `C` (`2^(2a+1) d^2 < n`) and the rest `R`: `d ↦ m / d` is a bijection `C → B`,
and `d ↦ 2^j d` (least `j` with `n ≤ 2 (2^j d)^2`) is a bijection from `R` onto the middle
divisors, since the window `n ≤ 2x^2 < 4n` contains exactly one of `d, 2d, 4d, ...`.
Hence A001227 = A067742 + 2 A131576, and `a(n) = A067742(n) + A131576(n)`.
-/

namespace OMA.A082647Proof

open OMA.S_oeis_a082647

lemma two_pow_odd_inj {i k d e : ℕ} (hd : Odd d) (he : Odd e) (h : 2 ^ i * d = 2 ^ k * e) :
    d = e := by
  rcases lt_trichotomy i k with hik | rfl | hik
  · exfalso
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hik
    rw [pow_add, pow_add, mul_assoc, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rw [h'] at hd
    have : Even (2 ^ t * (2 ^ 1 * e)) := ⟨2 ^ t * e, by ring⟩
    exact (Nat.not_even_iff_odd.2 hd) this
  · exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  · exfalso
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hik
    rw [pow_add, pow_add, mul_assoc, mul_assoc] at h
    have h' := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rw [← h'] at he
    have : Even (2 ^ t * (2 ^ 1 * d)) := ⟨2 ^ t * d, by ring⟩
    exact (Nat.not_even_iff_odd.2 he) this

lemma pow_le_of_dvd {a k m : ℕ} (hm : Odd m) (h : 2 ^ k ∣ 2 ^ a * m) : k ≤ a := by
  by_contra hc
  have h1 : 2 ^ (a + 1) ∣ 2 ^ a * m := (pow_dvd_pow 2 (by omega)).trans h
  rw [pow_succ, mul_comm (2 ^ a) 2, mul_comm (2 ^ a) m] at h1
  have h2 : 2 ∣ m := Nat.dvd_of_mul_dvd_mul_right (by positivity) h1
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h2)

lemma odd_dvd {a m d : ℕ} (hd : Odd d) (h : d ∣ 2 ^ a * m) : d ∣ m :=
  (Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hd)).dvd_of_dvd_mul_left h

lemma sq_ne_two_mul {d N : ℕ} (hd : Odd d) : d ^ 2 ≠ 2 * N := by
  intro h
  have : Odd (d ^ 2) := hd.pow
  rw [h] at this
  exact (Nat.not_even_iff_odd.2 this) ⟨N, by ring⟩

theorem key (n : ℕ) (hn : 1 ≤ n) :
    ((Nat.divisors n).filter (fun d => Odd d)).card =
      A067742 n + 2 * ((Nat.divisors n).filter (fun d => Odd d ∧ 2 * n < d ^ 2)).card := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hm0 : 0 < m := hm.pos
  have hN0 : 0 < 2 ^ a * m := by positivity
  set N := 2 ^ a * m with hN
  set O := (Nat.divisors N).filter (fun d => Odd d) with hO
  have hB : ((Nat.divisors N).filter (fun d => Odd d ∧ 2 * N < d ^ 2)).card =
      (O.filter (fun d => 2 * N < d ^ 2)).card := by
    rw [hO, Finset.filter_filter]
  have hsplit1 := Finset.card_filter_add_card_filter_not (s := O) (fun d => 2 * N < d ^ 2)
  set O' := O.filter (fun d => ¬ 2 * N < d ^ 2) with hO'
  have hsplit2 := Finset.card_filter_add_card_filter_not (s := O')
    (fun d => 2 ^ (2 * a + 1) * d ^ 2 < N)
  set C := O'.filter (fun d => 2 ^ (2 * a + 1) * d ^ 2 < N) with hC
  set R := O'.filter (fun d => ¬ 2 ^ (2 * a + 1) * d ^ 2 < N) with hR
  -- |C| = |B| via d ↦ m / d
  have hCB : C.card = (O.filter (fun d => 2 * N < d ^ 2)).card := by
    apply Finset.card_bij' (fun d _ => m / d) (fun e _ => m / e)
    · intro d hd
      simp only [hC, hO', hO, Finset.mem_filter, Nat.mem_divisors] at hd ⊢
      obtain ⟨⟨⟨⟨hdN, -⟩, hdo⟩, -⟩, hlt⟩ := hd
      obtain ⟨e, he⟩ := odd_dvd hdo hdN
      have hd0 : 0 < d := hdo.pos
      have he0 : 0 < e := by
        rcases Nat.eq_zero_or_pos e with h | h
        · rw [h, mul_zero] at he; omega
        · exact h
      rw [he, Nat.mul_div_cancel_left _ hd0]
      have heo : Odd e := (Nat.odd_mul.1 (he ▸ hm)).2
      have hlt' : 2 ^ (a + 1) * d < e := by
        have h1 : 2 ^ (2 * a + 1) * d ^ 2 < 2 ^ a * (d * e) := by rw [← he]; exact hlt
        have h2 : 2 ^ (2 * a + 1) * d ^ 2 = 2 ^ a * d * (2 ^ (a + 1) * d) := by ring
        have h3 : 2 ^ a * (d * e) = 2 ^ a * d * e := by ring
        rw [h2, h3] at h1
        exact Nat.lt_of_mul_lt_mul_left h1
      refine ⟨⟨⟨?_, hN0.ne'⟩, heo⟩, ?_⟩
      · rw [hN, he]; exact Dvd.intro_left (2 ^ a * d) (by ring)
      · rw [hN, he]
        have h4 : 2 * (2 ^ a * (d * e)) = (2 ^ (a + 1) * d) * e := by ring
        rw [h4, sq]
        exact Nat.mul_lt_mul_of_pos_right hlt' he0
    · intro e he
      simp only [hC, hO', hO, Finset.mem_filter, Nat.mem_divisors] at he ⊢
      obtain ⟨⟨⟨heN, -⟩, heo⟩, hlt⟩ := he
      obtain ⟨d, hd⟩ := odd_dvd heo heN
      have he0 : 0 < e := heo.pos
      have hd0 : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · rw [h, mul_zero] at hd; omega
        · exact h
      rw [hd, Nat.mul_div_cancel_left _ he0]
      have hdo : Odd d := (Nat.odd_mul.1 (hd ▸ hm)).2
      have hlt' : 2 ^ (a + 1) * d < e := by
        have h1 : 2 * (2 ^ a * (e * d)) < e ^ 2 := by rw [← hd]; exact hlt
        have h2 : 2 * (2 ^ a * (e * d)) = e * (2 ^ (a + 1) * d) := by ring
        rw [h2, sq] at h1
        exact Nat.lt_of_mul_lt_mul_left h1
      have hpow : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      have hpow1 : 2 ≤ 2 ^ (a + 1) := by
        rw [pow_succ]; omega
      refine ⟨⟨⟨⟨?_, hN0.ne'⟩, hdo⟩, ?_⟩, ?_⟩
      · rw [hN, hd]; exact Dvd.intro_left (2 ^ a * e) (by ring)
      · intro hc
        have h1 : 2 * (2 ^ a * (e * d)) < d ^ 2 := by rw [← hd]; exact hc
        have h4 : d ≤ e := by nlinarith
        have h5 : d ^ 2 ≤ e * d := by rw [sq]; exact Nat.mul_le_mul_right _ h4
        have h6 : e * d ≤ 2 ^ a * (e * d) := Nat.le_mul_of_pos_left _ (by positivity)
        omega
      · have h2 : 2 ^ (2 * a + 1) * d ^ 2 = 2 ^ a * d * (2 ^ (a + 1) * d) := by ring
        rw [h2, hN, hd, show 2 ^ a * (e * d) = 2 ^ a * d * e by ring]
        exact Nat.mul_lt_mul_of_pos_left hlt' (by positivity)
    · intro d hd
      simp only [hC, hO', hO, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨⟨⟨hdN, -⟩, hdo⟩, -⟩, -⟩ := hd
      exact Nat.div_div_self (odd_dvd hdo hdN) hm0.ne'
    · intro e he
      simp only [hO, Finset.mem_filter, Nat.mem_divisors] at he
      obtain ⟨⟨⟨heN, -⟩, heo⟩, -⟩ := he
      exact Nat.div_div_self (odd_dvd heo heN) hm0.ne'
  -- |R| = |Mid| via d ↦ 2^j d
  have hex : ∀ d, 0 < d → ∃ j, N ≤ 2 * (2 ^ j * d) ^ 2 := fun d hd =>
    ⟨N, by
      have h1 : N < 2 ^ N := Nat.lt_two_pow_self
      have h2 : 2 ^ N ≤ 2 ^ N * d := Nat.le_mul_of_pos_right _ hd
      have h3 : 2 ^ N * d ≤ (2 ^ N * d) ^ 2 := by
        rw [sq]; exact Nat.le_mul_of_pos_left _ (by positivity)
      omega⟩
  have hRpos : ∀ d ∈ R, 0 < d := by
    intro d hd
    simp only [hR, hO', hO, Finset.mem_filter] at hd
    exact hd.1.1.2.pos
  have hRM : R.card = A067742 N := by
    unfold A067742
    apply Finset.card_bij (fun d hd => 2 ^ (Nat.find (hex d (hRpos d hd))) * d)
    · intro d hd
      have hd' := hd
      simp only [hR, hO', hO, Finset.mem_filter, Nat.mem_divisors] at hd'
      obtain ⟨⟨⟨⟨hdN, -⟩, hdo⟩, hB'⟩, hC'⟩ := hd'
      have hd0 : 0 < d := hdo.pos
      have hspec : N ≤ 2 * (2 ^ Nat.find (hex d (hRpos d hd)) * d) ^ 2 :=
        Nat.find_spec (hex d (hRpos d hd))
      have hJa : Nat.find (hex d (hRpos d hd)) ≤ a := Nat.find_min' _ (by
        have h1 : 2 ^ (2 * a + 1) * d ^ 2 = 2 * (2 ^ a * d) ^ 2 := by ring
        omega)
      have hmin : ∀ j < Nat.find (hex d (hRpos d hd)), ¬ N ≤ 2 * (2 ^ j * d) ^ 2 :=
        fun j hj => Nat.find_min (hex d (hRpos d hd)) hj
      generalize Nat.find (hex d (hRpos d hd)) = J at hspec hJa hmin
      simp only [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨?_, hN0.ne'⟩, hspec, ?_⟩
      · exact Nat.mul_dvd_mul (pow_dvd_pow 2 hJa) (odd_dvd hdo hdN)
      · rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
        · rw [hJ0, pow_zero, one_mul]
          have hne := sq_ne_two_mul (N := N) hdo
          omega
        · have hm1 := hmin (J - 1) (by omega)
          have h1 : (2 ^ J * d) ^ 2 = 4 * (2 ^ (J - 1) * d) ^ 2 := by
            obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
            rw [show J' + 1 - 1 = J' by omega, pow_succ]
            ring
          omega
    · intro d1 hd1 d2 hd2 h
      have o1 : Odd d1 := by
        simp only [hR, hO', hO, Finset.mem_filter] at hd1; exact hd1.1.1.2
      have o2 : Odd d2 := by
        simp only [hR, hO', hO, Finset.mem_filter] at hd2; exact hd2.1.1.2
      exact two_pow_odd_inj o1 o2 h
    · intro x hx
      simp only [Finset.mem_filter, Nat.mem_divisors] at hx
      obtain ⟨⟨hxN, -⟩, hlo, hhi⟩ := hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        omega
      obtain ⟨k, o, ho, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hx0
      have ho0 : 0 < o := ho.pos
      have hka : k ≤ a := pow_le_of_dvd hm ((Dvd.intro _ rfl).trans hxN)
      have hoN : o ∣ N := (Dvd.intro_left _ rfl).trans hxN
      have hle : o ≤ 2 ^ k * o := Nat.le_mul_of_pos_left _ (by positivity)
      have hmem : o ∈ R := by
        simp only [hR, hO', hO, Finset.mem_filter, Nat.mem_divisors]
        refine ⟨⟨⟨⟨hoN, hN0.ne'⟩, ho⟩, ?_⟩, ?_⟩
        · have : o ^ 2 ≤ (2 ^ k * o) ^ 2 := Nat.pow_le_pow_left hle 2
          omega
        · have h1 : 2 ^ (2 * k + 1) * o ^ 2 ≤ 2 ^ (2 * a + 1) * o ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
          have h2 : 2 * (2 ^ k * o) ^ 2 = 2 ^ (2 * k + 1) * o ^ 2 := by ring
          omega
      refine ⟨o, hmem, ?_⟩
      have hJk : Nat.find (hex o (hRpos o hmem)) = k := by
        apply le_antisymm (Nat.find_min' (hex o (hRpos o hmem)) hlo)
        by_contra hlt
        rw [not_le] at hlt
        have hs := Nat.find_spec (hex o (hRpos o hmem))
        generalize Nat.find (hex o (hRpos o hmem)) = J at hs hlt
        obtain ⟨t, rfl⟩ : ∃ t, k = J + t + 1 := ⟨k - J - 1, by omega⟩
        have h1 : (2 ^ (J + t + 1) * o) ^ 2 = 4 ^ (t + 1) * (2 ^ J * o) ^ 2 := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          ring
        have h4 : 4 ≤ 4 ^ (t + 1) := Nat.le_self_pow (by omega) 4
        have h5 : 4 * (2 ^ J * o) ^ 2 ≤ (2 ^ (J + t + 1) * o) ^ 2 := by
          rw [h1]; exact Nat.mul_le_mul_right _ h4
        omega
      simp only [hJk]
  -- conclude
  rw [hB, ← hRM, ← hsplit1, ← hsplit2, hCB]
  ring

lemma sum2 (s d : ℕ) : (∑ i ∈ Finset.range d, (s + i)) * 2 = 2 * d * s + d * (d - 1) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, add_mul,
    Finset.sum_range_id_mul_two]
  ring

lemma consec_iff {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) :
    IsConsecSum n d ↔ Odd d ∧ d ^ 2 < 2 * n := by
  obtain ⟨q, rfl⟩ := hd
  constructor
  · rintro ⟨s, hs, hsum⟩
    have h2 := sum2 s d
    rw [hsum] at h2
    rcases d with _ | e
    · simp at hn
    have hq : q * 2 = 2 * s + e := by
      have h3 : (e + 1) * (q * 2) = (e + 1) * (2 * s + e) := by
        rw [show e + 1 - 1 = e by omega] at h2
        linarith [h2]
      exact Nat.eq_of_mul_eq_mul_left (by omega) h3
    refine ⟨⟨q - s, by omega⟩, ?_⟩
    have h4 : e + 1 < 2 * q := by omega
    calc (e + 1) ^ 2 = (e + 1) * (e + 1) := sq _
      _ < (e + 1) * (2 * q) := Nat.mul_lt_mul_of_pos_left h4 (by omega)
      _ = 2 * ((e + 1) * q) := by ring
  · rintro ⟨⟨t, ht⟩, hlt⟩
    subst ht
    have hlt' : 2 * t + 1 < 2 * q := by
      have h5 : (2 * t + 1) * (2 * t + 1) < (2 * t + 1) * (2 * q) := by
        rw [← sq]; linarith [hlt]
      exact Nat.lt_of_mul_lt_mul_left h5
    obtain ⟨u, rfl⟩ : ∃ u, q = t + 1 + u := ⟨q - t - 1, by omega⟩
    refine ⟨u + 1, by omega, ?_⟩
    have h2 := sum2 (u + 1) (2 * t + 1)
    rw [show 2 * t + 1 - 1 = 2 * t by omega] at h2
    have h6 : 2 * (2 * t + 1) * (u + 1) + (2 * t + 1) * (2 * t) = (2 * t + 1) * (t + 1 + u) * 2 := by
      ring
    rw [h6] at h2
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2

lemma a_eq (n : ℕ) (hn : 0 < n) :
    a n = ((Nat.divisors n).filter (fun d => Odd d ∧ d ^ 2 < 2 * n)).card := by
  classical
  unfold a
  congr 1
  apply Finset.filter_congr
  intro d hd
  exact consec_iff hn (Nat.dvd_of_mem_divisors hd)

lemma b_eq (n : ℕ) (hn : 0 < n) :
    A131576 n = ((Nat.divisors n).filter (fun d => Odd d ∧ 2 * n < d ^ 2)).card := by
  classical
  unfold A131576
  apply Finset.card_bij' (fun k _ => n / k) (fun o _ => n / o)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, -⟩, s, hs, hsum⟩ := hk
    have h2 := sum2 s (2 * k)
    rw [hsum] at h2
    have hn' : n = k * (2 * s + 2 * k - 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at h2
      rw [show 2 * s + 2 * (j + 1) - 1 = 2 * s + 2 * j + 1 by omega]
      have h7 : n * 2 = (j + 1) * (2 * s + 2 * j + 1) * 2 := by rw [h2]; ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h7
    set o := 2 * s + 2 * k - 1 with ho
    have hdiv : n / k = o := by
      rw [hn', Nat.mul_div_cancel_left _ (by omega)]
    rw [hdiv]
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨Dvd.intro_left k hn'.symm, hn.ne'⟩, ⟨s + k - 1, by omega⟩, ?_⟩
    have h8 : 2 * k < o := by omega
    calc 2 * n = (2 * k) * o := by rw [hn']; ring
      _ < o * o := Nat.mul_lt_mul_of_pos_right h8 (by omega)
      _ = o ^ 2 := (sq o).symm
  · intro o ho
    simp only [Finset.mem_filter, Nat.mem_divisors] at ho
    obtain ⟨⟨hon, -⟩, ⟨t, ht⟩, hlt⟩ := ho
    obtain ⟨k, hk⟩ := hon
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; omega
      · exact h
    have hdiv : n / o = k := by rw [hk, Nat.mul_div_cancel_left k (show 0 < o by omega)]
    rw [hdiv]
    have h9 : 2 * k < o := by
      have h10 : o * (2 * k) < o * o := by
        calc o * (2 * k) = 2 * n := by rw [hk]; ring
          _ < o ^ 2 := hlt
          _ = o * o := sq o
      exact Nat.lt_of_mul_lt_mul_left h10
    simp only [Finset.mem_filter, Finset.mem_Icc]
    obtain ⟨j, rfl⟩ : ∃ j, t = k + j := ⟨t - k, by omega⟩
    refine ⟨⟨hk0, ?_⟩, j + 1, by omega, ?_⟩
    · calc k ≤ o * k := Nat.le_mul_of_pos_left _ (by omega)
        _ = n := hk.symm
    · have h2 := sum2 (j + 1) (2 * k)
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at h2
      have h11 : 2 * (2 * (m + 1)) * (j + 1) + 2 * (m + 1) * (2 * m + 1) = n * 2 := by
        rw [hk, ht]; ring
      rw [h11] at h2
      exact Nat.eq_of_mul_eq_mul_right (m := 2) (by norm_num) h2
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk1, -⟩, s, hs, hsum⟩ := hk
    have h2 := sum2 s (2 * k)
    rw [hsum] at h2
    have hkn : k ∣ n := by
      refine ⟨2 * s + 2 * k - 1, ?_⟩
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega] at h2
      rw [show 2 * s + 2 * (j + 1) - 1 = 2 * s + 2 * j + 1 by omega]
      have h7 : n * 2 = (j + 1) * (2 * s + 2 * j + 1) * 2 := by rw [h2]; ring
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h7
    exact Nat.div_div_self hkn hn.ne'
  · intro o ho
    simp only [Finset.mem_filter, Nat.mem_divisors] at ho
    exact Nat.div_div_self ho.1.1 hn.ne'

end OMA.A082647Proof

open OMA.S_oeis_a082647 in
theorem OMA.solution : type_of% @OMA.S_oeis_a082647.main := by
  intro n hn
  have hk := OMA.A082647Proof.key n hn
  rw [OMA.A082647Proof.a_eq n (by omega), OMA.A082647Proof.b_eq n (by omega)]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Nat.divisors n).filter (fun d => Odd d)) (fun d => 2 * n < d ^ 2)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hS : ((Nat.divisors n).filter (fun d => Odd d ∧ ¬ 2 * n < d ^ 2)) =
      (Nat.divisors n).filter (fun d => Odd d ∧ d ^ 2 < 2 * n) := by
    apply Finset.filter_congr
    intro d _
    constructor
    · rintro ⟨hd, h⟩
      exact ⟨hd, lt_of_le_of_ne (not_lt.1 h) (OMA.A082647Proof.sq_ne_two_mul hd)⟩
    · rintro ⟨hd, h⟩
      exact ⟨hd, by omega⟩
  rw [hS] at hsplit
  unfold A001227
  constructor <;> omega
