import OMAStatements.S_oeis_a339387
import Mathlib

/-!
# A339387: equal sums force a squarefree `n`

With `g = gcd(n,k)`, `n = g a`, `k = g b`, the quotient `lcm/gcd` is `a b`, its residue modulo `k`
is `b (a mod g)` and modulo `n` it is `a (b mod g)` (`residues`). Pair `k` with `n - k` (same `g`,
`b` becomes `a - b`): the two gaps `fixed - varying` add up to `a (b mod g + (a-b) mod g - a mod g)`,
which is `≥ 0` (`pair_nonneg`). If `p^2 ∣ n`, the pair at `k = p` gives `a p > 0`. So `fixed n >
varying n` for every non-squarefree `n`.
-/

namespace OMA.A339387Proof
open OMA.S_oeis_a339387 Finset

/-- With `n = g a`, `k = g b` (`g = gcd n k`): the quotient is `a b`, and its residues are
`b (a mod g)` modulo `k` and `a (b mod g)` modulo `n`. -/
lemma residues {n k g a b : ℕ} (hg : 0 < g) (hn : n = g * a) (hk : k = g * b)
    (hgcd : n.gcd k = g) :
    quotient n k % k = b * (a % g) ∧ quotient n k % n = a * (b % g) := by
  have hq : quotient n k = a * b := by
    unfold quotient
    have h1 := Nat.gcd_mul_lcm n k
    rw [hgcd, hn, hk] at h1
    rw [hgcd]
    have h2 : Nat.lcm n k = g * (a * b) := by
      apply Nat.eq_of_mul_eq_mul_left hg
      rw [hn, hk, h1]; ring
    rw [h2, Nat.mul_div_cancel_left _ hg]
  rw [hq, hk, hn]
  constructor
  · rw [show a * b = b * a by ring, show g * b = b * g by ring, Nat.mul_mod_mul_left]
  · rw [show g * a = a * g by ring, Nat.mul_mod_mul_left]

/-- The integer gap at `k`: fixed residue minus varying residue. -/
def D (n k : ℕ) : ℤ := ((quotient n k % n : ℕ) : ℤ) - ((quotient n k % k : ℕ) : ℤ)

/-- Pairing `k` with `n - k`: the two gaps add up to `a (b mod g + (a-b) mod g - a mod g) ≥ 0`. -/
lemma pair {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) :
    D n k + D n (n - k) =
      ((n / n.gcd k : ℕ) : ℤ) * (((k / n.gcd k) % n.gcd k : ℕ) + (((n - k) / n.gcd k) % n.gcd k : ℕ)
        - ((n / n.gcd k) % n.gcd k : ℕ)) := by
  set g := n.gcd k with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left k (by omega)
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left n k
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right n k
  rw [← hgdef] at ha hb
  have hab : b ≤ a := by
    have : g * b ≤ g * a := by rw [← ha, ← hb]; omega
    exact Nat.le_of_mul_le_mul_left this hg
  have hnk : n - k = g * (a - b) := by rw [ha, hb, Nat.mul_sub]
  have hg2 : n.gcd (n - k) = g := by rw [Nat.gcd_self_sub_right hkn.le]
  obtain ⟨r1, r2⟩ := residues hg ha hb hgdef.symm
  obtain ⟨s1, s2⟩ := residues hg ha hnk hg2
  have e1 : n / g = a := by rw [ha, Nat.mul_div_cancel_left _ hg]
  have e2 : k / g = b := by rw [hb, Nat.mul_div_cancel_left _ hg]
  have e3 : (n - k) / g = a - b := by rw [hnk, Nat.mul_div_cancel_left _ hg]
  unfold D
  rw [r1, r2, s1, s2, e1, e2, e3]
  push_cast [Nat.cast_sub hab]
  ring

lemma pair_nonneg {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) : 0 ≤ D n k + D n (n - k) := by
  rw [pair hk1 hkn]
  set g := n.gcd k with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left k (by omega)
  -- `(x + y) % g ≤ x % g + y % g`, and `n / g ≡ k / g + (n - k) / g` modulo `g`
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left n k
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right n k
  rw [← hgdef] at ha hb
  have e1 : n / g = a := by rw [ha, Nat.mul_div_cancel_left _ hg]
  have e2 : k / g = b := by rw [hb, Nat.mul_div_cancel_left _ hg]
  have hab : b ≤ a := by rw [← e1, ← e2]; exact Nat.div_le_div_right (by omega)
  have hnk : n - k = g * (a - b) := by
    rw [Nat.mul_sub, show g * a = n from ha.symm, show g * b = k from hb.symm]
  have e3 : (n - k) / g = a - b := by
    rw [hnk, Nat.mul_div_cancel_left _ hg]
  rw [e1, e2, e3]
  have hmod : a % g ≤ b % g + (a - b) % g := by
    have h := Nat.add_mod b (a - b) g
    rw [show b + (a - b) = a by omega] at h
    rw [h]; exact Nat.mod_le _ _
  have : ((a % g : ℕ) : ℤ) ≤ ((b % g : ℕ) : ℤ) + (((a - b) % g : ℕ) : ℤ) := by exact_mod_cast hmod
  exact mul_nonneg (by positivity) (by linarith)

theorem main' : ∀ n : ℕ, 0 < n → varying n = fixed n → Squarefree n := by
  intro n hn heq
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  -- the total gap
  have hn1 : 2 ≤ n := by
    have := Nat.le_of_dvd hn hpp; have := hp.two_le; nlinarith
  have hp2 : 2 ≤ p := hp.two_le
  have hpn : p < n := by
    have := Nat.le_of_dvd hn hpp; nlinarith
  have htot : ((fixed n : ℕ) : ℤ) - ((varying n : ℕ) : ℤ) = ∑ k ∈ Ico 1 (n + 1), D n k := by
    unfold fixed varying D
    push_cast
    rw [← Finset.sum_sub_distrib]
  rw [heq, sub_self] at htot
  have hlast : D n n = 0 := by unfold D; ring
  rw [Finset.sum_Ico_succ_top (by omega), hlast, add_zero] at htot
  -- reflect: the same sum over `n - k`
  have hrefl : ∑ k ∈ Ico 1 n, D n (n - k) = ∑ k ∈ Ico 1 n, D n k := by
    rw [Finset.sum_Ico_reflect (fun j => D n j) 1 (show n ≤ n + 1 by omega),
      show n + 1 - n = 1 by omega, Nat.add_sub_cancel]
  have h2 : ∑ k ∈ Ico 1 n, (D n k + D n (n - k)) = 0 := by
    rw [Finset.sum_add_distrib, hrefl, ← htot]; ring
  -- but the pair at `k = p` is strictly positive
  have hpos : 0 < ∑ k ∈ Ico 1 n, (D n k + D n (n - k)) := by
    refine Finset.sum_pos' (fun k hk => by
      rw [Finset.mem_Ico] at hk; exact pair_nonneg hk.1 hk.2) ⟨p, Finset.mem_Ico.mpr ⟨by omega, hpn⟩, ?_⟩
    rw [pair (by omega) hpn]
    have hpd : p ∣ n := dvd_trans (Dvd.intro p rfl) hpp
    have hg : n.gcd p = p := Nat.gcd_eq_right hpd
    rw [hg, Nat.div_self (by omega)]
    obtain ⟨c, hc⟩ := hpp
    have e1 : n / p = p * c := by rw [hc, show p * p * c = p * (p * c) by ring, Nat.mul_div_cancel_left _ (by omega)]
    have e3 : (n - p) / p = p * c - 1 := by
      have h3 : n - p = p * (p * c - 1) := by rw [Nat.mul_sub_one, ← mul_assoc, ← hc]
      rw [h3, Nat.mul_div_cancel_left _ (by omega)]
    have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hc; omega)
    rw [e1, e3, Nat.mul_mod_right, Nat.one_mod_eq_one.mpr (by omega)]
    have hm : (p * c - 1) % p = p - 1 := by
      have : p * c - 1 = p * (c - 1) + (p - 1) := by
        obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
        rw [show c' + 1 - 1 = c' by omega, Nat.mul_succ]; omega
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    rw [hm]
    push_cast [Nat.cast_sub (show 1 ≤ p by omega)]
    have : (0 : ℤ) < (p : ℤ) * c := by positivity
    nlinarith
  linarith

end OMA.A339387Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a339387.main := OMA.A339387Proof.main'
