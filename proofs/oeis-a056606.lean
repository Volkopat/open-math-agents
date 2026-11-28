import OMAStatements.S_oeis_a056606
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic

namespace OMA.P_oeis_a056606

open OMA.S_oeis_a056606

private lemma lcm_choose_pos (n : ℕ) :
    0 < (Finset.range (n + 1)).lcm (fun k => Nat.choose n k) := by
  apply Nat.pos_of_ne_zero
  intro h0
  have hd : Nat.choose n 0 ∣ (Finset.range (n + 1)).lcm (fun k => Nat.choose n k) :=
    Finset.dvd_lcm (Finset.mem_range.mpr (Nat.succ_pos n))
  rw [Nat.choose_zero_right, h0] at hd
  have hmem : ∀ k ∈ Finset.range (n + 1), Nat.choose n k ≠ 0 := fun k hk =>
    Nat.ne_of_gt (Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
  have hne : (Finset.range (n + 1)).lcm (fun k => Nat.choose n k) ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    intro k hk
    exact hmem k hk
  exact hne h0

private lemma prime_dvd_finset_lcm {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ s.lcm f) : ∃ x ∈ s, p ∣ f x := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.lcm_empty] at hd
    have := Nat.le_of_dvd (by norm_num) hd
    have := hp.two_le
    omega
  | @insert a t hat ih =>
    rw [Finset.lcm_insert] at hd
    have hmul : p ∣ f a * t.lcm f := dvd_trans hd (Nat.lcm_dvd_mul (f a) (t.lcm f))
    rcases hp.dvd_mul.mp hmul with ha | ht
    · exact ⟨a, Finset.mem_insert_self a t, ha⟩
    · obtain ⟨x, hxt, hfx⟩ := ih ht
      exact ⟨x, Finset.mem_insert_of_mem hxt, hfx⟩

private lemma two_dvd_lcm_of_not_pow_two {n : ℕ} (hnot : ∀ m : ℕ, n + 1 ≠ 2 ^ m) :
    2 ∣ (Finset.range (n + 1)).lcm (fun k => Nat.choose n k) := by
  let r := Nat.factorization (n + 1) 2
  have hr_dvd : 2 ^ r ∣ n + 1 := Nat.ordProj_dvd (n + 1) 2
  rcases hr_dvd with ⟨q, hq⟩
  have hq_odd : ¬ 2 ∣ q := by
    intro h2q
    rcases h2q with ⟨c, rfl⟩
    have hpow : 2 ^ (r + 1) ∣ n + 1 := ⟨c, by rw [hq, pow_succ]; ring⟩
    have hle : r + 1 ≤ (n + 1).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).mp hpow
    omega
  have hq_ge3 : 3 ≤ q := by
    rcases Nat.eq_zero_or_pos q with rfl | hqp
    · omega
    · rcases eq_or_ne q 1 with rfl | hq1
      · exact absurd (by simpa using hq) (hnot r)
      · rcases eq_or_ne q 2 with rfl | hq2
        · exact absurd (dvd_refl 2) hq_odd
        · omega
  have hk_pos : 0 < 2 ^ r := Nat.pow_pos (by norm_num)
  have hk_le : 2 ^ r ≤ n := by
    have : 3 * 2 ^ r ≤ n + 1 := by nlinarith
    omega
  have hrec : Nat.choose n (2 ^ r) * 2 ^ r = Nat.choose n (2 ^ r - 1) * (n + 1 - 2 ^ r) := by
    have h1 := Nat.choose_succ_right_eq n (2 ^ r - 1)
    rw [show 2 ^ r - 1 + 1 = 2 ^ r by omega] at h1
    have h2 : n - (2 ^ r - 1) = n + 1 - 2 ^ r := by omega
    rw [h2] at h1
    exact h1
  have hsub : n + 1 - 2 ^ r = 2 ^ r * (q - 1) := by
    rw [hq, Nat.mul_sub_left_distrib, mul_one]
  rw [hsub, show Nat.choose n (2 ^ r - 1) * (2 ^ r * (q - 1)) =
    (Nat.choose n (2 ^ r - 1) * (q - 1)) * 2 ^ r by ring] at hrec
  have hceq : Nat.choose n (2 ^ r) = Nat.choose n (2 ^ r - 1) * (q - 1) :=
    Nat.eq_of_mul_eq_mul_right hk_pos hrec
  have h2_q1 : 2 ∣ q - 1 := by omega
  have h2_ch : 2 ∣ Nat.choose n (2 ^ r) := by
    rw [hceq]
    exact dvd_mul_of_dvd_right h2_q1 _
  exact dvd_trans h2_ch (Finset.dvd_lcm (Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le)))

private lemma odd_prime_dvd_lcm {n m p : ℕ} (hn : n + 1 = 2 ^ m) (hp : p.Prime)
    (hp2 : 2 < p) (hpn : p ≤ n) :
    p ∣ (Finset.range (n + 1)).lcm (fun k => Nat.choose n k) := by
  have hp_ndvd : ¬ p ∣ n + 1 := by
    intro hd
    rw [hn] at hd
    have h2 := hp.dvd_of_dvd_pow hd
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hmod_lt : n % p < p - 1 := by
    have hlt : n % p < p := Nat.mod_lt n hp.pos
    by_contra hge
    have heq : n % p = p - 1 := by omega
    have hdiv : p ∣ n + 1 := by
      refine ⟨n / p + 1, ?_⟩
      have hdm := Nat.div_add_mod n p
      have hmul : p * (n / p + 1) = p * (n / p) + p := by ring
      omega
    exact hp_ndvd hdiv
  let k := n % p + 1
  have hk_pos : 1 ≤ k := by omega
  have hk_lt_p : k < p := by omega
  have hk_le_n : k ≤ n := by omega
  have hrec : Nat.choose n k * k = Nat.choose n (k - 1) * (n + 1 - k) := by
    have h1 := Nat.choose_succ_right_eq n (k - 1)
    rw [show k - 1 + 1 = k by omega, show n - (k - 1) = n + 1 - k by omega] at h1
    exact h1
  have hp_sub : p ∣ n + 1 - k := by
    have h1 : n + 1 - k = n - n % p := by omega
    rw [h1]
    have h2 : n - n % p = p * (n / p) := by
      have := Nat.div_add_mod n p
      omega
    rw [h2]
    exact dvd_mul_right p (n / p)
  have hp_mul : p ∣ Nat.choose n k * k := by
    rw [hrec]
    exact dvd_mul_of_dvd_right hp_sub _
  have hp_ndvd_k : ¬ p ∣ k := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have hp_ch : p ∣ Nat.choose n k := (hp.dvd_mul.mp hp_mul).resolve_right hp_ndvd_k
  exact dvd_trans hp_ch (Finset.dvd_lcm (Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le_n)))

private theorem prove_main : type_of% @OMA.S_oeis_a056606.main := by
  intro n hodd
  set L := (Finset.range (n + 1)).lcm (fun k => Nat.choose n k)
  have hL_pos : 0 < L := lcm_choose_pos n
  have h2_ndvd_L : ¬ 2 ∣ L := by
    intro h2L
    have h2mem : 2 ∈ L.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2L, by omega⟩
    have h2_dvd_rad : 2 ∣ rad L := Finset.dvd_prod_of_mem (fun p => p) h2mem
    rcases hodd with ⟨t, ht⟩
    change rad L = 2 * t + 1 at ht
    omega
  have hpow2 : ∃ m : ℕ, n + 1 = 2 ^ m := by
    by_contra hnot
    push Not at hnot
    exact h2_ndvd_L (two_dvd_lcm_of_not_pow_two hnot)
  rcases hpow2 with ⟨m, hm⟩
  refine ⟨n, ?_⟩
  unfold a rad
  congr 1
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hp, hpL, _⟩
    obtain ⟨k, hk_mem, hpk⟩ := prime_dvd_finset_lcm (Finset.range (n + 1)) (fun k => Nat.choose n k) hp hpL
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem)
    have hp_le_n : p ≤ n := by
      have hd_fact : Nat.choose n k ∣ n.factorial := by
        have := Nat.choose_mul_factorial_mul_factorial hkn
        exact ⟨k.factorial * (n - k).factorial, by linarith⟩
      exact (hp.dvd_factorial.mp (dvd_trans hpk hd_fact))
    have hp2 : 2 < p := by
      have := hp.two_le
      have hne2 : p ≠ 2 := fun h => h2_ndvd_L (h ▸ hpL)
      omega
    exact ⟨Nat.lt_succ_of_le hp_le_n, hp, hp2⟩
  · rintro ⟨hpn, hp, hp2⟩
    exact ⟨hp, odd_prime_dvd_lcm hm hp hp2 (Nat.lt_succ_iff.mp hpn), by omega⟩

end OMA.P_oeis_a056606

theorem OMA.solution : type_of% @OMA.S_oeis_a056606.main :=
  OMA.P_oeis_a056606.prove_main
