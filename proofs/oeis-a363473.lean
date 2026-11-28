import OMAStatements.S_oeis_a363473
import Mathlib

namespace OMA.A363473Proof

open OMA.S_oeis_a363473

theorem gpf_mem {c : ℕ} (hc : 2 ≤ c) : gpf c ∈ c.primeFactors := by
  have hne : c.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup _ hne id
  unfold gpf
  rw [he]
  exact hi

theorem gpf_prime {c : ℕ} (hc : 2 ≤ c) : (gpf c).Prime := Nat.prime_of_mem_primeFactors (gpf_mem hc)

theorem gpf_dvd {c : ℕ} (hc : 2 ≤ c) : gpf c ∣ c := Nat.dvd_of_mem_primeFactors (gpf_mem hc)

theorem le_gpf {p c : ℕ} (hp : p.Prime) (hd : p ∣ c) (hc : c ≠ 0) : p ≤ gpf c := by
  unfold gpf
  exact Finset.le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hp, hd, hc⟩)

theorem gpf_le {c a : ℕ} (h : ∀ p, p.Prime → p ∣ c → p ≤ a) : gpf c ≤ a := by
  unfold gpf
  refine Finset.sup_le_iff.mpr ?_
  intro p hp
  have h' := Nat.mem_primeFactors.mp hp
  exact h p h'.1 h'.2.1

theorem gpf_mul {c q : ℕ} (hc : c ≠ 0) (hq : q.Prime) (h : gpf c ≤ q) : gpf (c * q) = q := by
  apply le_antisymm
  · apply gpf_le
    intro p hp hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
    · exact (le_gpf hp h1 hc).trans h
    · exact Nat.le_of_dvd hq.pos h1
  · exact le_gpf hq (dvd_mul_left q c) (mul_ne_zero hc hq.ne_zero)

theorem gpf_div_le {m : ℕ} (hm : 2 ≤ m) : gpf (m / gpf m) ≤ gpf m := by
  apply gpf_le
  intro p hp hd
  exact le_gpf hp (hd.trans (Nat.div_dvd_of_dvd (gpf_dvd hm))) (by omega)

theorem nth_mono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem pc_eq {p : ℕ} (hp : p.Prime) : Nat.primeCounting p = Nat.primeCounting' p + 1 := by
  rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting', Nat.count_succ, if_pos hp]

theorem idx {p : ℕ} (hp : p.Prime) : Nat.nth Nat.Prime (Nat.primeCounting' p) = p := Nat.nth_count hp

theorem gpf_key (c t : ℕ) (hc : 2 ≤ c) :
    gpf (c * Nat.nth Nat.Prime (t + Nat.primeCounting' (gpf c))) =
      Nat.nth Nat.Prime (t + Nat.primeCounting' (gpf c)) := by
  have hq := Nat.prime_nth_prime (t + Nat.primeCounting' (gpf c))
  refine gpf_mul (by omega) hq ?_
  calc gpf c = Nat.nth Nat.Prime (Nat.primeCounting' (gpf c)) := (idx (gpf_prime hc)).symm
    _ ≤ Nat.nth Nat.Prime (t + Nat.primeCounting' (gpf c)) := nth_mono.monotone (Nat.le_add_left _ _)

theorem prod_facts {c q : ℕ} (hc : 2 ≤ c) (hq : q.Prime) : c * q ≠ 1 ∧ ¬ (c * q).Prime := by
  have h3 := hq.two_le
  refine ⟨?_, Nat.not_prime_mul (by omega) hq.ne_one⟩
  intro h
  have h4 : 2 * 2 ≤ c * q := Nat.mul_le_mul hc h3
  rw [h] at h4
  omega

theorem gen (b : ℕ → ℕ) (hb : Set.BijOn b (Set.Ici 1) (Set.Ici 1)) (hb1 : b 1 = 1) :
    Set.BijOn (fun nk : ℕ × ℕ => Tb b nk.1 nk.2) {nk : ℕ × ℕ | 1 ≤ nk.2 ∧ nk.2 ≤ nk.1} (Set.Ici 1) := by
  have hb2 : ∀ k, 2 ≤ k → 2 ≤ b k := by
    intro k hk
    have h1 : 1 ≤ b k := Set.mem_Ici.mp (hb.mapsTo (Set.mem_Ici.mpr (by omega : 1 ≤ k)))
    by_contra hcon
    have hbk : b k = b 1 := by rw [hb1]; omega
    have := hb.injOn (Set.mem_Ici.mpr (by omega : 1 ≤ k)) (Set.mem_Ici.mpr le_rfl) hbk
    omega
  have hT : ∀ n k, 2 ≤ k → k ≤ n →
      Tb b n k = b k * Nat.nth Nat.Prime ((n - k) + Nat.primeCounting' (gpf (b k))) := by
    intro n k hk hkn
    have hg := gpf_prime (hb2 k hk)
    have hk1 : k ≠ 1 := by omega
    rw [Tb, if_neg hk1, prime, A061395, pc_eq hg,
      show n - k + (Nat.primeCounting' (gpf (b k)) + 1) - 1 = n - k + Nat.primeCounting' (gpf (b k)) by omega]
  have hT1 : ∀ n, 2 ≤ n → Tb b n 1 = Nat.nth Nat.Prime (n - 2) := by
    intro n hn
    have hn1 : n ≠ 1 := by omega
    rw [Tb, if_pos rfl, A008578, if_neg hn1, prime, show n - 1 - 1 = n - 2 by omega]
  have hT11 : Tb b 1 1 = 1 := by
    rw [Tb, if_pos rfl, A008578, if_pos rfl]
  have comp : ∀ n k, 2 ≤ k → k ≤ n → Tb b n k ≠ 1 ∧ ¬ (Tb b n k).Prime := by
    intro n k hk hkn
    rw [hT n k hk hkn]
    exact prod_facts (hb2 k hk) (Nat.prime_nth_prime _)
  have col : ∀ n, 1 ≤ n → Tb b n 1 = 1 ∨ (Tb b n 1).Prime := by
    intro n hn
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      exact Or.inl hT11
    · right
      rw [hT1 n h]
      exact Nat.prime_nth_prime _
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo
    rintro ⟨n, k⟩ ⟨hk1, hkn⟩
    change 1 ≤ k at hk1
    change k ≤ n at hkn
    show 1 ≤ Tb b n k
    rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      rcases col n hkn with h | h
      · exact le_of_eq h.symm
      · exact h.one_lt.le
    · rw [hT n k hk hkn]
      exact Nat.mul_pos (by have := hb2 k hk; omega) (Nat.prime_nth_prime _).pos
  · -- InjOn
    rintro ⟨n1, k1⟩ ⟨h11, h12⟩ ⟨n2, k2⟩ ⟨h21, h22⟩ heq
    change 1 ≤ k1 at h11
    change k1 ≤ n1 at h12
    change 1 ≤ k2 at h21
    change k2 ≤ n2 at h22
    change Tb b n1 k1 = Tb b n2 k2 at heq
    rcases Nat.lt_or_ge k1 2 with hk1 | hk1 <;> rcases Nat.lt_or_ge k2 2 with hk2 | hk2
    · obtain rfl : k1 = 1 := by omega
      obtain rfl : k2 = 1 := by omega
      rcases Nat.lt_or_ge n1 2 with hn1 | hn1 <;> rcases Nat.lt_or_ge n2 2 with hn2 | hn2
      · obtain rfl : n1 = 1 := by omega
        obtain rfl : n2 = 1 := by omega
        rfl
      · exfalso
        obtain rfl : n1 = 1 := by omega
        rw [hT11, hT1 n2 hn2] at heq
        exact (Nat.prime_nth_prime (n2 - 2)).ne_one heq.symm
      · exfalso
        obtain rfl : n2 = 1 := by omega
        rw [hT11, hT1 n1 hn1] at heq
        exact (Nat.prime_nth_prime (n1 - 2)).ne_one heq
      · rw [hT1 n1 hn1, hT1 n2 hn2] at heq
        have hi := nth_mono.injective heq
        have : n1 = n2 := by omega
        rw [this]
    · exfalso
      obtain rfl : k1 = 1 := by omega
      have hc := comp n2 k2 hk2 h22
      rcases col n1 h12 with h | h
      · exact hc.1 (heq.symm.trans h)
      · exact hc.2 (by rw [← heq]; exact h)
    · exfalso
      obtain rfl : k2 = 1 := by omega
      have hc := comp n1 k1 hk1 h12
      rcases col n2 h22 with h | h
      · exact hc.1 (heq.trans h)
      · exact hc.2 (by rw [heq]; exact h)
    · rw [hT n1 k1 hk1 h12, hT n2 k2 hk2 h22] at heq
      have hp2 := Nat.prime_nth_prime ((n2 - k2) + Nat.primeCounting' (gpf (b k2)))
      have hg1 := gpf_key (b k1) (n1 - k1) (hb2 k1 hk1)
      have hg2 := gpf_key (b k2) (n2 - k2) (hb2 k2 hk2)
      have hq := hg1.symm.trans ((congrArg gpf heq).trans hg2)
      have hc : b k1 = b k2 := by
        rw [hq] at heq
        exact Nat.eq_of_mul_eq_mul_right hp2.pos heq
      have hk : k1 = k2 := hb.injOn (Set.mem_Ici.mpr h11) (Set.mem_Ici.mpr h21) hc
      subst hk
      have hi := nth_mono.injective hq
      have : n1 = n2 := by omega
      subst this
      rfl
  · -- SurjOn
    intro m hm
    have hm1 : 1 ≤ m := Set.mem_Ici.mp hm
    rcases Nat.lt_or_ge m 2 with h | h
    · obtain rfl : m = 1 := by omega
      exact ⟨(1, 1), ⟨le_rfl, le_rfl⟩, hT11⟩
    · have hp := gpf_prime h
      have hpd := gpf_dvd h
      have hcm : m / gpf m * gpf m = m := Nat.div_mul_cancel hpd
      have hj := idx hp
      rcases Nat.lt_or_ge (m / gpf m) 2 with hc | hc
      · have hc1 : m / gpf m = 1 := by
          rcases Nat.lt_or_ge (m / gpf m) 1 with h0 | h0
          · have h00 : m / gpf m = 0 := Nat.lt_one_iff.mp h0
            rw [h00] at hcm
            omega
          · omega
        refine ⟨(Nat.primeCounting' (gpf m) + 2, 1),
          ⟨le_rfl, (by omega : 1 ≤ Nat.primeCounting' (gpf m) + 2)⟩, ?_⟩
        show Tb b (Nat.primeCounting' (gpf m) + 2) 1 = m
        rw [hT1 (Nat.primeCounting' (gpf m) + 2) (by omega), Nat.add_sub_cancel, hj]
        rw [hc1, one_mul] at hcm
        exact hcm
      · obtain ⟨k, hk, hbk⟩ := hb.surjOn (Set.mem_Ici.mpr (by omega : 1 ≤ m / gpf m))
        have hk1 : 1 ≤ k := Set.mem_Ici.mp hk
        have hk2 : 2 ≤ k := by
          rcases Nat.lt_or_ge k 2 with h' | h'
          · exfalso
            obtain rfl : k = 1 := by omega
            rw [hb1] at hbk
            omega
          · exact h'
        have hgle : gpf (m / gpf m) ≤ gpf m := gpf_div_le h
        have hpi : Nat.primeCounting' (gpf (m / gpf m)) ≤ Nat.primeCounting' (gpf m) :=
          Nat.monotone_primeCounting' hgle
        obtain ⟨n, hn⟩ : ∃ n, n = Nat.primeCounting' (gpf m) - Nat.primeCounting' (gpf (m / gpf m)) + k :=
          ⟨_, rfl⟩
        refine ⟨(n, k), ⟨hk1, (by omega : k ≤ n)⟩, ?_⟩
        show Tb b n k = m
        rw [hT n k hk2 (by omega), hbk,
          show n - k + Nat.primeCounting' (gpf (m / gpf m)) = Nat.primeCounting' (gpf m) by omega, hj]
        exact hcm

theorem special :
    Set.BijOn (fun nk : ℕ × ℕ => A363473 nk.1 nk.2) {nk : ℕ × ℕ | 1 ≤ nk.2 ∧ nk.2 ≤ nk.1} (Set.Ici 1) := by
  have e : (fun nk : ℕ × ℕ => A363473 nk.1 nk.2) = (fun nk : ℕ × ℕ => Tb id nk.1 nk.2) := by
    funext nk
    rfl
  rw [e]
  exact gen id (Set.bijOn_id _) rfl

end OMA.A363473Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a363473.main :=
  ⟨OMA.A363473Proof.special, fun b hb hb1 => OMA.A363473Proof.gen b hb hb1⟩
