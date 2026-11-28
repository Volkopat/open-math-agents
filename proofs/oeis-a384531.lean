import OMAStatements.S_oeis_a384531
import Mathlib
open OMA.S_oeis_a384531

def a384531_G (n j : ℕ) : ℕ := Nat.gcd j n * Nat.gcd (j+1) n
def a384531_F (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, a384531_G n j

theorem a384531_G_mod (n j : ℕ) : a384531_G n (j % n) = a384531_G n j := by
  unfold a384531_G
  have h1 : j % n ≡ j [MOD n] := Nat.mod_modEq j n
  have h2 : j % n + 1 ≡ j + 1 [MOD n] := Nat.ModEq.add_right 1 h1
  rw [Nat.ModEq.gcd_eq h1, Nat.ModEq.gcd_eq h2]

theorem a384531_G_mul (m k j : ℕ) (h : Nat.Coprime m k) :
    a384531_G (m*k) j = a384531_G m j * a384531_G k j := by
  unfold a384531_G
  rw [Nat.Coprime.gcd_mul _ h, Nat.Coprime.gcd_mul _ h]; ring

theorem a384531_F_mul (m k : ℕ) (h : Nat.Coprime m k) :
    a384531_F (m*k) = a384531_F m * a384531_F k := by
  unfold a384531_F
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hinj : Set.InjOn (fun j => (j % m, j % k)) (Finset.range (m*k) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio, Prod.mk.injEq] at hx hy hxy
    have : x ≡ y [MOD m*k] := (Nat.modEq_and_modEq_iff_modEq_mul h).1 ⟨hxy.1, hxy.2⟩
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  have himg : (Finset.range (m*k)).image (fun j => (j % m, j % k)) =
      Finset.range m ×ˢ Finset.range k := by
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      simp only [Finset.mem_image, Finset.mem_range] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      simp only [Finset.mem_product, Finset.mem_range]
      have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
      have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hj)
      exact ⟨Nat.mod_lt _ hm, Nat.mod_lt _ hk⟩
    · rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
        Finset.card_range, Finset.card_range]
  rw [← himg, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro j _
  simp only
  rw [a384531_G_mod, a384531_G_mod, a384531_G_mul _ _ _ h]

theorem a384531_shift (n : ℕ) (g : ℕ → ℕ) (hg : g n = g 0) :
    ∑ i ∈ Finset.range n, g (i+1) = ∑ i ∈ Finset.range n, g i := by
  have := Finset.sum_range_succ g n
  rw [Finset.sum_range_succ'] at this
  omega

theorem a384531_pillai (n : ℕ) (hn : n ≠ 0) :
    ∑ i ∈ Finset.range n, Nat.gcd n i = ∑ k ∈ n.divisors, Nat.totient k * (n / k) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => Nat.gcd n i) (t := n.divisors)]
  · rw [← Nat.sum_div_divisors n]
    apply Finset.sum_congr rfl
    intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const,
      ← Nat.totient_div_of_dvd (Nat.div_dvd_of_dvd hdn), Nat.div_div_self hdn hn, smul_eq_mul,
      mul_comm]
  · intro i _
    simp [Nat.mem_divisors, Nat.gcd_dvd_left, hn]

theorem a384531_pillai_pp (p e : ℕ) (hp : p.Prime) :
    ∑ j ∈ Finset.range (p^e), Nat.gcd j (p^e) = p^e + e * (p^(e-1) * (p-1)) := by
  have hpe : p^e ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [Finset.sum_congr rfl (fun j _ => Nat.gcd_comm j (p^e)), a384531_pillai _ hpe,
    Nat.divisors_prime_pow hp, Finset.sum_map, Finset.sum_range_succ']
  simp only [Function.Embedding.coeFn_mk, pow_zero, Nat.totient_one, Nat.div_one, one_mul]
  rw [add_comm]; congr 1
  rw [Finset.sum_congr rfl (g := fun _ => p^(e-1)*(p-1)), Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Nat.totient_prime_pow_succ hp, Nat.pow_div (by omega) hp.pos]
  calc p ^ i * (p - 1) * p ^ (e - (i + 1)) = p ^ (i + (e - (i+1))) * (p - 1) := by ring
    _ = p ^ (e - 1) * (p - 1) := by congr 2; omega

theorem a384531_G_pp (p e j : ℕ) (hp : p.Prime) :
    a384531_G (p^e) j + 1 = Nat.gcd j (p^e) + Nat.gcd (j+1) (p^e) := by
  unfold a384531_G
  by_cases hj : p ∣ j
  · have : ¬ p ∣ j+1 := fun h => hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hj).1 h))
    have hc : Nat.gcd (j+1) (p^e) = 1 :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 this).symm
    rw [hc]; ring
  · have hc : Nat.gcd j (p^e) = 1 :=
      Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hj).symm
    rw [hc]; ring

theorem a384531_F_pp (p e : ℕ) (hp : p.Prime) :
    a384531_F (p^e) + p^e = 2 * (p^e + e * (p^(e-1) * (p-1))) := by
  have h1 : ∑ j ∈ Finset.range (p^e), (a384531_G (p^e) j + 1) = a384531_F (p^e) + p^e := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]; rfl
  have h2 := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range (p^e)) => a384531_G_pp p e j hp)
  have hs := a384531_shift (p^e) (fun j => Nat.gcd j (p^e)) (by simp)
  rw [h1, Finset.sum_add_distrib, hs, a384531_pillai_pp p e hp] at h2
  rw [h2]; ring

theorem a384531_F_pp' (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    a384531_F (p^k) = ((2*k+1)*p - 2*k) * p^(k-1) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k-1, by omega⟩
  have h := a384531_F_pp p (k+1) hp
  simp only [Nat.add_sub_cancel] at h ⊢
  have hp2 := hp.two_le
  have hle : 2*(k+1) ≤ (2*(k+1)+1)*p := by nlinarith
  have hp1 : 1 ≤ p := hp.one_lt.le
  zify [hle, hp1] at h ⊢
  rw [pow_succ] at h ⊢
  linear_combination h

theorem OMA.solution : type_of% @OMA.S_oeis_a384531.main := by
  intro n hn
  have hR : ∑ i ∈ Finset.range n, (i+1).gcd n * (i+2).gcd n = a384531_F n :=
    a384531_shift n (a384531_G n) (by rw [← a384531_G_mod n n, Nat.mod_self])
  have hF1 : a384531_F 1 = 1 := by decide
  rw [hR, Nat.multiplicative_factorization a384531_F a384531_F_mul hF1 hn.ne']
  unfold a
  rw [Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hk : 1 ≤ n.factorization p :=
    Nat.Prime.factorization_pos_of_dvd hpp hn.ne' (Nat.dvd_of_mem_primeFactors hp)
  rw [a384531_F_pp' p _ hpp hk]
