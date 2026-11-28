import OMAReductions.R_AgohGiuga_agoh_giuga_R1_H2_R1

/-!
Proof of `OMA.R_AgohGiuga_agoh_giuga_R1_H2_R1.H1`.
Let `n` be a strong Giuga number and `p` a prime factor, `n = p * m`. Reducing modulo `p`, the
sum of `i ^ (n - 1)` over `0 < i < n` is `m` times the power sum over `ZMod p`, which is `-1`
when `p - 1 ∣ n - 1` and `0` otherwise. Since `n` divides one plus that sum, `p - 1 ∣ n - 1`
and `m ≡ 1 (mod p)`. In particular `p ∤ m`, so `n` is squarefree, and Korselt's criterion
(`AgohGiuga.korselts_criterion`) shows that `n` is a Carmichael number.
-/

namespace OMAProof.GiugaPowerSums

open Finset

theorem sum_pow_zmod {p : ℕ} [Fact p.Prime] (k : ℕ) (hk : k ≠ 0) :
    ∑ x : ZMod p, x ^ k = if p - 1 ∣ k then -1 else 0 := by
  classical
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using! isUnit_iff_ne_zero
  have hu := FiniteField.sum_pow_units (ZMod p) k
  rw [ZMod.card] at hu
  calc ∑ x : ZMod p, x ^ k = ∑ x ∈ univ \ {(0 : ZMod p)}, x ^ k := by
        rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton, zero_pow hk,
          add_zero]
    _ = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ k) := by simp [φ, ← hmap, univ.sum_map φ]
    _ = _ := hu

theorem sum_range_eq_univ {p : ℕ} [NeZero p] (f : ZMod p → ZMod p) :
    ∑ j ∈ range p, f (j : ZMod p) = ∑ x : ZMod p, f x := by
  apply Finset.sum_nbij (fun j : ℕ => (j : ZMod p))
  · intro a _; exact mem_univ _
  · intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' a b p).mp hab
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro x _
    exact ⟨x.val, by simp [ZMod.val_lt], ZMod.natCast_zmod_val x⟩
  · intro a _; rfl

theorem sum_range_mul (p m k : ℕ) :
    (∑ i ∈ range (p * m), ((i : ℕ) : ZMod p) ^ k) =
      (m : ZMod p) * ∑ j ∈ range p, ((j : ℕ) : ZMod p) ^ k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have h : ∀ x : ℕ, ((p * m + x : ℕ) : ZMod p) = (x : ZMod p) := by
      intro x; push_cast; simp
    simp only [h]
    push_cast
    ring

/-- The core congruences: for a strong Giuga number `n` and a prime `p ∣ n`,
`p - 1 ∣ n - 1` and `n / p ≡ 1 (mod p)`. -/
theorem core {n p : ℕ} (hn : AgohGiuga.IsStrongGiuga n) (hp : p.Prime) (hpn : p ∣ n) :
    p - 1 ∣ n - 1 ∧ ((n / p : ℕ) : ZMod p) = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hn1, _⟩, hdiv⟩ := hn
  have hk : n - 1 ≠ 0 := by omega
  have h0 : ((1 + ∑ i ∈ Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (hpn.trans hdiv)
  have hIoo : ∑ i ∈ Ioo 0 n, ((i : ℕ) : ZMod p) ^ (n - 1) =
      ∑ i ∈ range n, ((i : ℕ) : ZMod p) ^ (n - 1) := by
    rw [Finset.sum_range_eq_add_Ico _ (by omega)]
    simp only [Nat.cast_zero, zero_pow hk, zero_add]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext x; simp only [mem_Ioo, mem_Ico]; omega
  obtain ⟨m, rfl⟩ := hpn
  have hm : (p * m) / p = m := Nat.mul_div_cancel_left m hp.pos
  rw [hm]
  push_cast at h0
  rw [hIoo, sum_range_mul, sum_range_eq_univ (fun x => x ^ (p * m - 1)),
    sum_pow_zmod _ hk] at h0
  by_cases hd : p - 1 ∣ p * m - 1
  · rw [if_pos hd] at h0
    refine ⟨hd, ?_⟩
    linear_combination -h0
  · rw [if_neg hd, mul_zero, add_zero] at h0
    exact absurd h0 one_ne_zero

end OMAProof.GiugaPowerSums

open OMAProof.GiugaPowerSums in
theorem OMA.solution : OMA.R_AgohGiuga_agoh_giuga_R1_H2_R1.H1 := by
  intro n hn
  have hc : n.Composite := hn.1
  refine (AgohGiuga.korselts_criterion n hc).mpr ⟨?_, fun p hp hpn => (core hn hp hpn).1⟩
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := (Dvd.intro p rfl).trans hpp
  have h1 := (core hn hp hpn).2
  have h2 : p ∣ n / p := Nat.dvd_div_of_mul_dvd hpp
  have : Fact p.Prime := ⟨hp⟩
  rw [(ZMod.natCast_eq_zero_iff _ _).mpr h2] at h1
  exact zero_ne_one h1

