import OMAStatements.S_oeis_a219562
import Mathlib

/-!
# Proof of OEIS A219562, Supercongruence Conjecture (Peter Bala)

Official OEIS entry [A219562](https://oeis.org/A219562):
$$a(n) = \sum_{k=0}^{n} \binom{n + k}{k}^4.$$
Matthijs Coster proved in *Supercongruences* (Theorem 4) that $a(p - 1) \equiv 1 \pmod{p^3}$
for all primes $p \ge 5$.
Conjecture ([OEIS A219562](https://oeis.org/A219562), Peter Bala): For all primes $p \ge 7$,
$$a(p - 1) \equiv 1 \pmod{p^5}.$$

## Proof Overview (100% elementary, zero `sorry`, zero custom axioms)
For $k = 0$, $\binom{p - 1}{0}^4 = 1$. For every $1 \le k \le p - 1$:
1. Using the rising-factorial identity $k! \binom{p - 1 + k}{k} = \prod_{j=0}^{k-1} (p + j) = p \prod_{j=1}^{k-1} (p + j)$,
   since $p \nmid k!$, we have $p \mid \binom{p - 1 + k}{k}$.
2. Writing $c_k = \binom{p - 1 + k}{k} / p \in \mathbb{N}$, we get
   $k! \cdot c_k = \prod_{j=1}^{k-1} (p + j) \equiv (k - 1)! \pmod p$,
   and cancelling the unit $(k - 1)! \in (\mathbb{Z}/p\mathbb{Z})^\times$ yields
   $k \cdot c_k \equiv 1 \pmod p$, i.e., $c_k \equiv k^{-1} \pmod p$.
3. Therefore
   $$a(p - 1) - 1 = \sum_{k=1}^{p-1} (p \cdot c_k)^4 = p^4 \sum_{k=1}^{p-1} c_k^4.$$
4. In $\mathbb{Z}/p\mathbb{Z}$, $\sum_{k=1}^{p-1} c_k^4 = \sum_{x \in (\mathbb{Z}/p\mathbb{Z})^\times} x^{-4} = 0$
   for all primes $p \ge 7$ (by the bijection $x \mapsto 2x$, giving $(2^4 - 1) \sum x^{-4} = 15 \sum x^{-4} = 0$,
   and $p \nmid 15$ for $p \ge 7$).
5. Hence $p \mid \sum_{k=1}^{p-1} c_k^4$, so $p^5 \mid (a(p - 1) - 1)$.
-/

namespace SolvedConjecture10

open Finset BigOperators

/-- OEIS A219562: $a(n) = \sum_{k=0}^{n} \binom{n + k}{k}^4$. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), ((n + k).choose k) ^ 4

/-- Rising-factorial identity: $k! \binom{n + k}{k} = \prod_{j=0}^{k-1} (n + 1 + j)$. -/
private lemma factorial_mul_choose_add (n k : ℕ) :
    k.factorial * (n + k).choose k = ∏ j ∈ Finset.range k, (n + 1 + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ← ih, Nat.factorial_succ]
    have hch : (n + (k + 1)).choose (k + 1) * (k + 1) = (n + k).choose k * (n + k + 1) := by
      have h1 := Nat.add_one_mul_choose_eq (n + k) k
      rw [show n + (k + 1) = n + k + 1 by omega]
      linarith
    calc (k + 1) * k.factorial * (n + (k + 1)).choose (k + 1)
        = k.factorial * ((n + (k + 1)).choose (k + 1) * (k + 1)) := by ring
      _ = k.factorial * ((n + k).choose k * (n + k + 1)) := by rw [hch]
      _ = k.factorial * (n + k).choose k * (n + 1 + k) := by ring

/-- For prime $p$ and $1 \le k \le p - 1$, $p \mid \binom{p - 1 + k}{k}$. -/
private lemma prime_dvd_choose_sub_one_add {p k : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k < p) :
    p ∣ (p - 1 + k).choose k := by
  have hfac := factorial_mul_choose_add (p - 1) k
  have h0 : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  rw [← Finset.mul_prod_erase _ _ h0, add_zero, Nat.sub_add_cancel hp.one_le] at hfac
  have hdvd : p ∣ k.factorial * (p - 1 + k).choose k := ⟨_, hfac⟩
  have hndvd : ¬ p ∣ k.factorial := fun h => by
    have := hp.dvd_factorial.mp h; omega
  exact (hp.dvd_mul.mp hdvd).resolve_left hndvd

/-- For prime $p \ge 7$, $\sum_{k=1}^{p-1} (k^{-1})^4 = 0$ in $\mathbb{Z}/p\mathbb{Z}$. -/
private lemma sum_inv_pow4_mod_p {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 4 = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := fun h => by
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff 2 p).mp h); omega
  have h15ne : (15 : ZMod p) ≠ 0 := fun h => by
    have hd : p ∣ 15 := (ZMod.natCast_eq_zero_iff 15 p).mp h
    have h15 : p ∣ 3 * 5 := hd
    rcases hp.dvd_mul.mp h15 with h3 | h5
    · have := Nat.le_of_dvd (by decide) h3; omega
    · have := Nat.le_of_dvd (by decide) h5; omega
  have hbij : ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 4 = ∑ x : ZMod p, (x⁻¹) ^ 4 := by
    symm
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
    simp only [inv_zero, zero_pow (by norm_num : 4 ≠ 0), zero_add]
    refine Finset.sum_nbij (fun x => x.val) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      simp only [Finset.mem_Icc]
      have hpos : 0 < x.val := Nat.pos_of_ne_zero fun h => hx ((ZMod.val_eq_zero x).mp h)
      have hlt : x.val < p := x.val_lt
      omega
    · intro a _ b _ h; exact ZMod.val_injective p h
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_Icc] at hk
      refine ⟨(k : ZMod p), ?_, ZMod.val_natCast_of_lt (by omega)⟩
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]
      intro h0
      exact Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
    · intro x _; rw [ZMod.natCast_zmod_val]
  rw [hbij]
  have hscale : ∑ x : ZMod p, ((2 * x)⁻¹) ^ 4 = ∑ x : ZMod p, (x⁻¹) ^ 4 :=
    Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) h2ne) (fun x => (x⁻¹) ^ 4)
  have h16 : ∑ x : ZMod p, ((2 * x)⁻¹) ^ 4 = ((2 : ZMod p)⁻¹) ^ 4 * ∑ x : ZMod p, (x⁻¹) ^ 4 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by rw [mul_inv, mul_pow]
  rw [h16] at hscale
  have hmul16 : (16 : ZMod p) * (((2 : ZMod p)⁻¹) ^ 4 * ∑ x : ZMod p, (x⁻¹) ^ 4) =
      ∑ x : ZMod p, (x⁻¹) ^ 4 := by
    have : (16 : ZMod p) * ((2 : ZMod p)⁻¹) ^ 4 = 1 := by
      calc (16 : ZMod p) * ((2 : ZMod p)⁻¹) ^ 4 = ((2 : ZMod p) * (2 : ZMod p)⁻¹) ^ 4 := by ring
        _ = 1 ^ 4 := by rw [mul_inv_cancel₀ h2ne]
        _ = 1 := one_pow 4
    rw [← mul_assoc, this, one_mul]
  have h15s : (15 : ZMod p) * ∑ x : ZMod p, (x⁻¹) ^ 4 = 0 := by
    have := congrArg ((16 : ZMod p) * ·) hscale
    rw [hmul16] at this
    linear_combination -this
  exact (mul_eq_zero.mp h15s).resolve_left h15ne

/--
**OEIS A219562, Supercongruence Conjecture (Peter Bala):**
For all primes $p \ge 7$, $a(p - 1) \equiv 1 \pmod{p^5}$, i.e., $p^5 \mid (a(p - 1) - 1)$.
-/
theorem conjecture_1 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    p ^ 5 ∣ (a (p - 1) - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  -- Split off k = 0 from a (p - 1)
  have hsplit : a (p - 1) = 1 + ∑ k ∈ Finset.Icc 1 (p - 1), ((p - 1 + k).choose k) ^ 4 := by
    unfold a
    rw [Nat.sub_add_cancel hp.one_le]
    have h0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
    rw [← Finset.add_sum_erase _ _ h0, Nat.choose_zero_right, one_pow]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext k; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]; omega
  rw [hsplit, Nat.add_sub_cancel_left]
  -- Factor out p^4 from every term k ∈ Icc 1 (p - 1)
  have hfactor : ∑ k ∈ Finset.Icc 1 (p - 1), ((p - 1 + k).choose k) ^ 4 =
      p ^ 4 * ∑ k ∈ Finset.Icc 1 (p - 1), ((p - 1 + k).choose k / p) ^ 4 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    have hdvd := prime_dvd_choose_sub_one_add hp hk.1 (Nat.lt_of_le_pred hp.pos hk.2)
    rw [← mul_pow, Nat.mul_div_cancel' hdvd]
  rw [hfactor]
  -- Show p ∣ ∑ k ∈ Icc 1 (p - 1), ((p - 1 + k).choose k / p) ^ 4
  have hdvd_sum : p ∣ ∑ k ∈ Finset.Icc 1 (p - 1), ((p - 1 + k).choose k / p) ^ 4 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    push_cast
    have hterm : ∀ k ∈ Finset.Icc 1 (p - 1),
        (((p - 1 + k).choose k / p : ℕ) : ZMod p) ^ 4 = ((k : ZMod p)⁻¹) ^ 4 := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hkp : k < p := Nat.lt_of_le_pred hp.pos hk.2
      have hck : (((p - 1 + k).choose k / p : ℕ) : ZMod p) = (k : ZMod p)⁻¹ := by
        have hfac := factorial_mul_choose_add (p - 1) k
        have h0 : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
        rw [← Finset.mul_prod_erase _ _ h0, add_zero, Nat.sub_add_cancel hp.one_le] at hfac
        have hdvd := prime_dvd_choose_sub_one_add hp hk.1 hkp
        have hnat : k.factorial * ((p - 1 + k).choose k / p) =
            ∏ j ∈ (Finset.range k).erase 0, (p + j) := by
          apply Nat.eq_of_mul_eq_mul_left hp.pos
          calc p * (k.factorial * ((p - 1 + k).choose k / p))
              = k.factorial * (p * ((p - 1 + k).choose k / p)) := by ring
            _ = k.factorial * (p - 1 + k).choose k := by rw [Nat.mul_div_cancel' hdvd]
            _ = p * ∏ j ∈ (Finset.range k).erase 0, (p + j) := hfac
        have hZ := congrArg (Nat.cast (R := ZMod p)) hnat
        push_cast at hZ
        have hprodZ : ∏ j ∈ (Finset.range k).erase 0, ((p : ZMod p) + (j : ZMod p)) =
            (((k - 1).factorial : ℕ) : ZMod p) := by
          have hset : (Finset.range k).erase 0 = Finset.Icc 1 (k - 1) := by
            ext j; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]; omega
          rw [hset]
          have hzero : ∀ j ∈ Finset.Icc 1 (k - 1), ((p : ZMod p) + (j : ZMod p)) = (j : ZMod p) := by
            intro j _; rw [ZMod.natCast_self, zero_add]
          rw [Finset.prod_congr rfl hzero, ← Nat.cast_prod]
          congr 1
          clear hzero hset hZ hnat hfac hdvd
          have hfac_prod : ∀ m : ℕ, ∏ j ∈ Finset.Icc 1 m, j = m.factorial := by
            intro m
            induction m with
            | zero => simp
            | succ m ih =>
              have hmem : m + 1 ∈ Finset.Icc 1 (m + 1) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
              rw [← Finset.mul_prod_erase _ _ hmem]
              have herase : (Finset.Icc 1 (m + 1)).erase (m + 1) = Finset.Icc 1 m := by
                ext j; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
              rw [herase, ih, Nat.factorial_succ]
          exact hfac_prod (k - 1)
        rw [hprodZ] at hZ
        have hkfac : k.factorial = k * (k - 1).factorial := by
          conv_lhs => rw [← Nat.sub_add_cancel hk.1]
          rw [Nat.factorial_succ, Nat.sub_add_cancel hk.1]
        rw [hkfac] at hZ; push_cast at hZ
        have hfnz : (((k - 1).factorial : ℕ) : ZMod p) ≠ 0 := fun h => by
          have := hp.dvd_factorial.mp ((ZMod.natCast_eq_zero_iff _ p).mp h); omega
        have hkne : (k : ZMod p) ≠ 0 := fun h =>
          Nat.not_dvd_of_pos_of_lt hk.1 hkp ((ZMod.natCast_eq_zero_iff k p).mp h)
        have hkc : (k : ZMod p) * (((p - 1 + k).choose k / p : ℕ) : ZMod p) = 1 := by
          apply mul_right_cancel₀ hfnz
          rw [one_mul]; linear_combination hZ
        calc (((p - 1 + k).choose k / p : ℕ) : ZMod p)
            = (k : ZMod p)⁻¹ * ((k : ZMod p) * (((p - 1 + k).choose k / p : ℕ) : ZMod p)) := by
                rw [← mul_assoc, inv_mul_cancel₀ hkne, one_mul]
          _ = (k : ZMod p)⁻¹ := by rw [hkc, mul_one]
      rw [hck]
    rw [Finset.sum_congr rfl hterm, sum_inv_pow4_mod_p hp hp7]
  exact dvd_trans (dvd_of_eq (by ring)) (mul_dvd_mul_left (p ^ 4) hdvd_sum)


end SolvedConjecture10

/-!
OEIS A219562, prime-power supercongruence (conjecture of Peter Bala):
for `a(n) = Sum_{k=0..n} binomial(n+k, k)^4`, every prime `p >= 5` and every `r >= 2`,
`p^(3r+3)` divides `a(p^r - 1) - a(p^(r-1) - 1)`.

Proof outline. Put `N = p^r`, `M = p^(r-1)`, `B_N(k) = C(N-1+k, k)`, and let `I(k)` be the set of
`i < k` not divisible by `p`.
* Terms with `p` not dividing `k`: `B_N(k) = N c_k` with `k c_k = 1 (mod p)`, and the sum of `k^(-4)`
  over `I(p^r)` vanishes mod `p` (it is `p^(r-1)` times a sum over one period), so these terms give
  `p^(4r+1)`.
* Terms `k = p j`: `U B_N(pj) = V B_M(j)` with `U = Prod_{I(k)} i`, `V = Prod_{I(k)} (N+i)`.
  Pairing `i` with `k - i` gives `(N+i)(N+k-i) = i(k-i) + N(N+k)`, hence
  `V^2 = U^2 Prod (1 + N(N+k) / (i(k-i)))` in the `p`-adic integers, and only
  `G(k) = Sum_{I(k)} 1/(i(k-i))` matters. For `k = t q`, `q = p^m`, a block decomposition gives
  `G(tq) = -t (S2(q) + q S3(q)) (mod q^2)`, where `S2(q) = Sum_{I(q)} u^(-2)` is divisible by `q`
  (the map `x -> 2x` permutes `ZMod q` and `3` is a unit). So
  `B_N(pj)^2 = B_M(j)^2 (1 + N q^2 (-t^2 sigma + p h))`.
* If `p^(r-2)` does not divide `j`, this and `v_p(B_M(j)) >= r-1-v_p(j)` give `p^(3r+3)` termwise.
* On the top layer `j = c p^(r-2)`, `B_M(j) = p beta_c` with `c beta_c = 1 (mod p)`; each term is
  `-2 sigma c^2 beta_c^4 p^(3r+2) (mod p^(3r+3))` and `Sum_c c^(-2) = 0 (mod p)`.
No Jacobsthal-type congruence is used.
-/

namespace A219562H2

/-- The index set `{i < k : ¬ p ∣ i}`. -/
private def Iset (p k : ℕ) : Finset ℕ := (Finset.range k).filter (fun i => ¬ p ∣ i)

private lemma mem_Iset {p k i : ℕ} : i ∈ Iset p k ↔ i < k ∧ ¬ p ∣ i := by
  simp [Iset]

/-! Splitting a range by divisibility -/

private lemma filter_dvd_range (d j : ℕ) (hd : 0 < d) :
    (Finset.range (d * j)).filter (fun i => d ∣ i) = (Finset.range j).image (fun l => d * l) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hi, l, rfl⟩
    exact ⟨l, lt_of_mul_lt_mul_left hi (Nat.zero_le d), rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨Nat.mul_lt_mul_of_pos_left hl hd, dvd_mul_right d l⟩

private lemma sum_range_split {A : Type*} [AddCommMonoid A] (d j : ℕ) (hd : 0 < d) (f : ℕ → A) :
    ∑ i ∈ Finset.range (d * j), f i =
      ∑ i ∈ (Finset.range (d * j)).filter (fun i => ¬ d ∣ i), f i +
        ∑ l ∈ Finset.range j, f (d * l) := by
  have h := Finset.sum_filter_add_sum_filter_not (Finset.range (d * j)) (fun i => d ∣ i) f
  rw [filter_dvd_range d j hd,
    Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hd hab)] at h
  rw [← h]
  exact add_comm _ _

private lemma sum_range_split' {A : Type*} [AddCommMonoid A] (d j n : ℕ) (hd : 0 < d)
    (hn : n = d * j) (f : ℕ → A) :
    ∑ i ∈ Finset.range n, f i =
      ∑ i ∈ (Finset.range n).filter (fun i => ¬ d ∣ i), f i +
        ∑ l ∈ Finset.range j, f (d * l) := by
  subst hn
  exact sum_range_split d j hd f

private lemma prod_range_split {A : Type*} [CommMonoid A] (p j : ℕ) (hp : 0 < p) (f : ℕ → A) :
    ∏ i ∈ Finset.range (p * j), f i =
      (∏ i ∈ Iset p (p * j), f i) * ∏ l ∈ Finset.range j, f (p * l) := by
  have h := Finset.prod_filter_mul_prod_filter_not (Finset.range (p * j)) (fun i => p ∣ i) f
  rw [filter_dvd_range p j hp,
    Finset.prod_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left hp hab)] at h
  rw [← h]
  exact mul_comm _ _

/-! Reflection `i ↦ k - i` on the index set -/

private lemma prod_Iset_reflect {A : Type*} [CommMonoid A] {p k : ℕ} (hpk : p ∣ k) (f : ℕ → A) :
    ∏ i ∈ Iset p k, f (k - i) = ∏ i ∈ Iset p k, f i := by
  have key : ∀ i ∈ Iset p k, k - i ∈ Iset p k := by
    intro i hi
    rw [mem_Iset] at hi ⊢
    have hi0 : i ≠ 0 := fun h => hi.2 (h ▸ dvd_zero p)
    refine ⟨by omega, fun h => hi.2 ?_⟩
    have h2 : p ∣ (k - i) + i := by
      rw [Nat.sub_add_cancel (le_of_lt hi.1)]; exact hpk
    exact (Nat.dvd_add_right h).mp h2
  have inv : ∀ i ∈ Iset p k, k - (k - i) = i := by
    intro i hi
    rw [mem_Iset] at hi
    omega
  exact Finset.prod_nbij' (fun i => k - i) (fun i => k - i) key key inv inv (fun _ _ => rfl)

/-! Blocks of length `q` -/

private lemma sum_blocks {A : Type*} [AddCommMonoid A] {p q : ℕ} (hpq : p ∣ q) (f : ℕ → A)
    (t : ℕ) :
    ∑ i ∈ Iset p (t * q), f i = ∑ b ∈ Finset.range t, ∑ u ∈ Iset p q, f (b * q + u) := by
  induction t with
  | zero => simp [Iset]
  | succ t ih =>
    rw [Finset.sum_range_succ, ← ih]
    unfold Iset
    simp only [Finset.sum_filter]
    rw [add_one_mul, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    have h : p ∣ t * q + x ↔ p ∣ x := Nat.dvd_add_right (Dvd.dvd.mul_left hpq t)
    simp only [h]

/-! Binomial identities -/

private lemma factorial_mul_choose (n k : ℕ) :
    k.factorial * (n + k).choose k = ∏ i ∈ Finset.range k, (n + 1 + i) := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose, Nat.ascFactorial_eq_prod_range]

private lemma factorial_eq_prod_reflect (n : ℕ) :
    n.factorial = ∏ i ∈ Finset.range n, (n - i) := by
  rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self]

/-- The unit parts: `U * C(pM - 1 + pj, pj) = V * C(M - 1 + j, j)`. -/
private lemma choose_units_relation {p M j : ℕ} (hp : 0 < p) (hM : 1 ≤ M) :
    (∏ i ∈ Iset p (p * j), i) * (p * M - 1 + p * j).choose (p * j) =
      (∏ i ∈ Iset p (p * j), (p * M + i)) * (M - 1 + j).choose j := by
  have hfac : (p * j).factorial = (∏ i ∈ Iset p (p * j), i) * (p ^ j * j.factorial) := by
    rw [factorial_eq_prod_reflect (p * j), prod_range_split p j hp, factorial_eq_prod_reflect j]
    congr 1
    · exact prod_Iset_reflect (dvd_mul_right p j) (fun x => x)
    · calc ∏ l ∈ Finset.range j, (p * j - p * l) = ∏ l ∈ Finset.range j, (p * (j - l)) :=
            Finset.prod_congr rfl (fun l _ => (mul_tsub p j l).symm)
        _ = p ^ j * ∏ l ∈ Finset.range j, (j - l) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hrise : ∏ i ∈ Finset.range (p * j), (p * M + i) =
      (∏ i ∈ Iset p (p * j), (p * M + i)) * (p ^ j * (j.factorial * (M - 1 + j).choose j)) := by
    rw [prod_range_split p j hp, factorial_mul_choose (M - 1) j]
    congr 1
    calc ∏ l ∈ Finset.range j, (p * M + p * l) = ∏ l ∈ Finset.range j, (p * (M + l)) :=
          Finset.prod_congr rfl (fun l _ => (mul_add p M l).symm)
      _ = p ^ j * ∏ l ∈ Finset.range j, (M - 1 + 1 + l) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
            Nat.sub_add_cancel hM]
  have hN : ∏ i ∈ Finset.range (p * j), (p * M + i) =
      (p * j).factorial * (p * M - 1 + p * j).choose (p * j) := by
    rw [factorial_mul_choose (p * M - 1) (p * j), Nat.sub_add_cancel (Nat.mul_pos hp hM)]
  have hpos : 0 < p ^ j * j.factorial := Nat.mul_pos (pow_pos hp j) (Nat.factorial_pos j)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc p ^ j * j.factorial * ((∏ i ∈ Iset p (p * j), i) * (p * M - 1 + p * j).choose (p * j))
      = (p * j).factorial * (p * M - 1 + p * j).choose (p * j) := by rw [hfac]; ring
    _ = ∏ i ∈ Finset.range (p * j), (p * M + i) := hN.symm
    _ = p ^ j * j.factorial *
          ((∏ i ∈ Iset p (p * j), (p * M + i)) * (M - 1 + j).choose j) := by rw [hrise]; ring

private lemma mul_choose_eq {M j : ℕ} (hM : 1 ≤ M) (hj : 1 ≤ j) :
    j * (M - 1 + j).choose j = M * (M + (j - 1)).choose (j - 1) := by
  have h := Nat.choose_succ_right_eq (M - 1 + j) (j - 1)
  rw [Nat.sub_add_cancel hj] at h
  have e1 : M - 1 + j - (j - 1) = M := by omega
  have e2 : M + (j - 1) = M - 1 + j := by omega
  rw [e1] at h
  rw [e2]
  linarith

private lemma choose_pow_add_modp {p m n : ℕ} (hp : p.Prime) (hn : n < p ^ m) :
    (((p ^ m + n).choose n : ℕ) : ZMod p) = 1 := by
  rw [Nat.add_choose_eq, Nat.cast_sum]
  rw [Finset.sum_eq_single (0, n)]
  · simp
  · rintro ⟨i, l⟩ hil hne
    have hil' : i + l = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hil
    have hi0 : i ≠ 0 := by
      rintro rfl
      apply hne
      have : l = n := by omega
      rw [this]
    have hilt : i ≠ p ^ m := by omega
    have hd := hp.dvd_choose_pow hi0 hilt
    show ((((p ^ m).choose i * n.choose l : ℕ)) : ZMod p) = 0
    rw [Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).mpr hd, zero_mul]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.zero_add n)) h

/-! Product expansion to first order -/

private lemma prod_one_add_expand {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (z : R)
    (f : ι → R) :
    ∃ d : R, ∏ i ∈ s, (1 + z * f i) = 1 + z * ∑ i ∈ s, f i + z ^ 2 * d := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + f a * ∑ i ∈ s, f i + z * f a * d, ?_⟩
    rw [Finset.prod_insert ha, Finset.sum_insert ha, hd]
    ring

/-! Inverses and ring homomorphisms -/

private lemma map_ring_inverse' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {x : R}
    (hx : IsUnit x) : φ (Ring.inverse x) = Ring.inverse (φ x) := by
  have h1 : φ x * φ (Ring.inverse x) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel x hx, map_one]
  have h2 : IsUnit (φ x) := hx.map φ
  calc φ (Ring.inverse x) = Ring.inverse (φ x) * φ x * φ (Ring.inverse x) := by
        rw [Ring.inverse_mul_cancel _ h2, one_mul]
    _ = Ring.inverse (φ x) * (φ x * φ (Ring.inverse x)) := by ring
    _ = Ring.inverse (φ x) := by rw [h1, mul_one]

private lemma sum_inverse_sq_zmod (q : ℕ) [NeZero q] (h2 : IsUnit (2 : ZMod q))
    (h3 : IsUnit (3 : ZMod q)) :
    ∑ x : ZMod q, (Ring.inverse x) ^ 2 = 0 := by
  obtain ⟨u2, hu2⟩ := h2
  have hperm : ∑ x : ZMod q, (Ring.inverse ((u2 : ZMod q) * x)) ^ 2 =
      ∑ x : ZMod q, (Ring.inverse x) ^ 2 :=
    Equiv.sum_comp (Units.mulLeft u2) (fun x => (Ring.inverse x) ^ 2)
  have hfac : ∑ x : ZMod q, (Ring.inverse ((u2 : ZMod q) * x)) ^ 2 =
      (Ring.inverse (u2 : ZMod q)) ^ 2 * ∑ x : ZMod q, (Ring.inverse x) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Ring.mul_inverse_rev]; ring
  have h22 : (2 : ZMod q) * Ring.inverse (u2 : ZMod q) = 1 := by
    rw [← hu2]; exact Ring.mul_inverse_cancel _ u2.isUnit
  have h3S : (3 : ZMod q) * ∑ x : ZMod q, (Ring.inverse x) ^ 2 = 0 := by
    have h := hperm.symm.trans hfac
    linear_combination 4 * h +
      ((2 * Ring.inverse (u2 : ZMod q) + 1) * ∑ x : ZMod q, (Ring.inverse x) ^ 2) * h22
  calc ∑ x : ZMod q, (Ring.inverse x) ^ 2
      = Ring.inverse (3 : ZMod q) * ((3 : ZMod q) * ∑ x : ZMod q, (Ring.inverse x) ^ 2) := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ h3, one_mul]
    _ = 0 := by rw [h3S, mul_zero]

/-! `p`-adic integers -/

private lemma isUnit_intCast_padic {p : ℕ} [Fact p.Prime] {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) :
    IsUnit (z : PadicInt p) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hz ?_)
  exact (PadicInt.norm_int_lt_one_iff_dvd z).mp h

private lemma isUnit_natCast_padic {p : ℕ} [Fact p.Prime] {i : ℕ} (hi : ¬ p ∣ i) :
    IsUnit (i : PadicInt p) := by
  have h : ¬ (p : ℤ) ∣ (i : ℤ) := fun h => hi (Int.natCast_dvd_natCast.mp h)
  have := isUnit_intCast_padic (p := p) h
  rwa [Int.cast_natCast] at this

private lemma S2_dvd {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (m : ℕ) (hm : 1 ≤ m) :
    (p : PadicInt p) ^ m ∣ ∑ u ∈ Iset p (p ^ m), (Ring.inverse (u : PadicInt p)) ^ 2 := by
  have hpp := hp.out
  have : NeZero (p ^ m) := ⟨pow_ne_zero m hpp.ne_zero⟩
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sum]
  have step1 : ∀ u ∈ Iset p (p ^ m),
      (PadicInt.toZModPow m) ((Ring.inverse (u : PadicInt p)) ^ 2) =
        (Ring.inverse ((u : ℕ) : ZMod (p ^ m))) ^ 2 := by
    intro u hu
    rw [map_pow, map_ring_inverse' _ (isUnit_natCast_padic (mem_Iset.mp hu).2), map_natCast]
  rw [Finset.sum_congr rfl step1]
  have step2 : ∑ u ∈ Iset p (p ^ m), (Ring.inverse ((u : ℕ) : ZMod (p ^ m))) ^ 2 =
      ∑ u ∈ Finset.range (p ^ m), (Ring.inverse ((u : ℕ) : ZMod (p ^ m))) ^ 2 := by
    unfold Iset
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hd : p ∣ u
    · have hnu : ¬ IsUnit ((u : ℕ) : ZMod (p ^ m)) := by
        rw [ZMod.isUnit_iff_coprime]
        intro hc
        have hc' : Nat.Coprime u p :=
          Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) hc
        exact (hpp.coprime_iff_not_dvd.mp hc'.symm) hd
      simp [hd, Ring.inverse_non_unit _ hnu]
    · simp [hd]
  rw [step2]
  have step3 : ∑ u ∈ Finset.range (p ^ m), (Ring.inverse ((u : ℕ) : ZMod (p ^ m))) ^ 2 =
      ∑ x : ZMod (p ^ m), (Ring.inverse x) ^ 2 := by
    refine Finset.sum_nbij' (fun u => ((u : ℕ) : ZMod (p ^ m))) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intro u _; exact Finset.mem_univ _
    · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
    · intro u hu; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hu)
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro u _; rfl
  rw [step3]
  apply sum_inverse_sq_zmod
  · have h : IsUnit ((2 : ℕ) : ZMod (p ^ m)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact Nat.Coprime.pow_right m ((Nat.coprime_primes Nat.prime_two hpp).mpr (by omega))
    simpa using h
  · have h : IsUnit ((3 : ℕ) : ZMod (p ^ m)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact Nat.Coprime.pow_right m ((Nat.coprime_primes Nat.prime_three hpp).mpr (by omega))
    simpa using h

/-! The pairing identity and the block formula, in a ring where `p`-free integers are units -/

private lemma isUnit_nat_of_int {R : Type*} [CommRing R] {p : ℕ}
    (hR : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → IsUnit (z : R)) {i : ℕ} (hi : ¬ p ∣ i) : IsUnit (i : R) := by
  have h := hR (i : ℤ) (fun h => hi (Int.natCast_dvd_natCast.mp h))
  rwa [Int.cast_natCast] at h

private lemma isUnit_sub_of_int {R : Type*} [CommRing R] {p : ℕ}
    (hR : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → IsUnit (z : R)) {k i : ℕ} (hk : p ∣ k) (hi : ¬ p ∣ i) :
    IsUnit ((k : R) - (i : R)) := by
  have h := hR ((k : ℤ) - (i : ℤ)) (fun h => hi (by
    have hk' : (p : ℤ) ∣ (k : ℤ) := Int.natCast_dvd_natCast.mpr hk
    have h2 : (p : ℤ) ∣ (i : ℤ) := by
      have h3 := dvd_sub hk' h
      rwa [sub_sub_cancel] at h3
    exact Int.natCast_dvd_natCast.mp h2))
  rwa [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at h

private lemma pair_prod {R : Type*} [CommRing R] {p : ℕ}
    (hR : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → IsUnit (z : R)) {k : ℕ} (hpk : p ∣ k) (N : ℕ) :
    (∏ i ∈ Iset p k, ((N : R) + (i : R))) ^ 2 =
      (∏ i ∈ Iset p k, (i : R)) ^ 2 *
        ∏ i ∈ Iset p k, (1 + ((N : R) * ((N : R) + (k : R))) *
          (Ring.inverse (i : R) * Ring.inverse ((k : R) - (i : R)))) := by
  have hV : ∏ i ∈ Iset p k, ((N : R) + ((k - i : ℕ) : R)) =
      ∏ i ∈ Iset p k, ((N : R) + (i : R)) :=
    prod_Iset_reflect hpk (fun x => (N : R) + (x : R))
  have hU : ∏ i ∈ Iset p k, ((k - i : ℕ) : R) = ∏ i ∈ Iset p k, (i : R) :=
    prod_Iset_reflect hpk (fun x => (x : R))
  calc (∏ i ∈ Iset p k, ((N : R) + (i : R))) ^ 2
      = (∏ i ∈ Iset p k, ((N : R) + ((k - i : ℕ) : R))) *
          ∏ i ∈ Iset p k, ((N : R) + (i : R)) := by rw [hV, pow_two]
    _ = ∏ i ∈ Iset p k, ((((k - i : ℕ) : R) * (i : R)) *
          (1 + ((N : R) * ((N : R) + (k : R))) *
            (Ring.inverse (i : R) * Ring.inverse ((k : R) - (i : R))))) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [mem_Iset] at hi
        have h1 : (i : R) * Ring.inverse (i : R) = 1 :=
          Ring.mul_inverse_cancel _ (isUnit_nat_of_int hR hi.2)
        have h2 : ((k : R) - (i : R)) * Ring.inverse ((k : R) - (i : R)) = 1 :=
          Ring.mul_inverse_cancel _ (isUnit_sub_of_int hR hpk hi.2)
        rw [Nat.cast_sub (le_of_lt hi.1)]
        linear_combination
          (-((N : R) * ((N : R) + (k : R))) * (((k : R) - (i : R)) *
            Ring.inverse ((k : R) - (i : R)))) * h1 + (-((N : R) * ((N : R) + (k : R)))) * h2
    _ = ((∏ i ∈ Iset p k, ((k - i : ℕ) : R)) * ∏ i ∈ Iset p k, (i : R)) *
          ∏ i ∈ Iset p k, (1 + ((N : R) * ((N : R) + (k : R))) *
            (Ring.inverse (i : R) * Ring.inverse ((k : R) - (i : R)))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = _ := by rw [hU, pow_two]

private lemma inv_pair_identity {R : Type*} [CommRing R] (u ui a ai c ci A B : R)
    (hu : u * ui = 1) (ha : a * ai = 1) (hc : c * ci = 1) (haA : a = A + u) (hcB : c = B - u) :
    ai * ci = -ui ^ 2 - (B - A) * ui ^ 3 +
      ui ^ 3 * (ai * ci) * (u * A * B + (B - A) * A * B + u * (B - A) ^ 2) := by
  subst haA hcB
  have e1 : ai * ci = (ui ^ 3 * (ai * ci)) * u ^ 3 := by
    calc ai * ci = ai * ci * (u * ui) ^ 3 := by rw [hu, one_pow, mul_one]
      _ = (ui ^ 3 * (ai * ci)) * u ^ 3 := by ring
  have e2 : ui ^ 2 = (ui ^ 3 * (ai * ci)) * (u * ((A + u) * (B - u))) := by
    calc ui ^ 2 = ui ^ 2 * (u * ui) * (((A + u) * ai) * ((B - u) * ci)) := by
          rw [hu, ha, hc]; ring
      _ = (ui ^ 3 * (ai * ci)) * (u * ((A + u) * (B - u))) := by ring
  have e3 : ui ^ 3 = (ui ^ 3 * (ai * ci)) * ((A + u) * (B - u)) := by
    calc ui ^ 3 = ui ^ 3 * (((A + u) * ai) * ((B - u) * ci)) := by rw [ha, hc]; ring
      _ = (ui ^ 3 * (ai * ci)) * ((A + u) * (B - u)) := by ring
  linear_combination e1 + e2 + (B - A) * e3

private lemma G1_inner {R : Type*} [CommRing R] {p q : ℕ}
    (hR : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → IsUnit (z : R)) (hpq : p ∣ q) (t b : ℕ) :
    ∃ g : R, ∑ u ∈ Iset p q, Ring.inverse ((b * q + u : ℕ) : R) *
        Ring.inverse (((t * q : ℕ) : R) - ((b * q + u : ℕ) : R)) =
      -(∑ u ∈ Iset p q, Ring.inverse (u : R) ^ 2) -
        (((t : R) - 2 * (b : R)) * (q : R)) * (∑ u ∈ Iset p q, Ring.inverse (u : R) ^ 3) +
        (q : R) ^ 2 * g := by
  refine ⟨∑ u ∈ Iset p q, Ring.inverse (u : R) ^ 3 *
      (Ring.inverse ((b * q + u : ℕ) : R) *
        Ring.inverse (((t * q : ℕ) : R) - ((b * q + u : ℕ) : R))) *
      ((u : R) * (b : R) * ((t : R) - (b : R)) +
        ((t : R) - 2 * (b : R)) * (q : R) * (b : R) * ((t : R) - (b : R)) +
        (u : R) * ((t : R) - 2 * (b : R)) ^ 2), ?_⟩
  have pointwise : ∀ u ∈ Iset p q, Ring.inverse ((b * q + u : ℕ) : R) *
        Ring.inverse (((t * q : ℕ) : R) - ((b * q + u : ℕ) : R)) =
      -(Ring.inverse (u : R) ^ 2) -
        (((t : R) - 2 * (b : R)) * (q : R)) * (Ring.inverse (u : R) ^ 3) +
        (q : R) ^ 2 * (Ring.inverse (u : R) ^ 3 *
          (Ring.inverse ((b * q + u : ℕ) : R) *
            Ring.inverse (((t * q : ℕ) : R) - ((b * q + u : ℕ) : R))) *
          ((u : R) * (b : R) * ((t : R) - (b : R)) +
            ((t : R) - 2 * (b : R)) * (q : R) * (b : R) * ((t : R) - (b : R)) +
            (u : R) * ((t : R) - 2 * (b : R)) ^ 2)) := by
    intro u hu
    rw [mem_Iset] at hu
    have hbu : ¬ p ∣ b * q + u := fun h =>
      hu.2 ((Nat.dvd_add_right (Dvd.dvd.mul_left hpq b)).mp h)
    have h1 : (u : R) * Ring.inverse (u : R) = 1 :=
      Ring.mul_inverse_cancel _ (isUnit_nat_of_int hR hu.2)
    have h2 : ((b * q + u : ℕ) : R) * Ring.inverse ((b * q + u : ℕ) : R) = 1 :=
      Ring.mul_inverse_cancel _ (isUnit_nat_of_int hR hbu)
    have h3 : (((t * q : ℕ) : R) - ((b * q + u : ℕ) : R)) *
        Ring.inverse (((t * q : ℕ) : R) - ((b * q + u : ℕ) : R)) = 1 :=
      Ring.mul_inverse_cancel _ (isUnit_sub_of_int hR (Dvd.dvd.mul_left hpq t) hbu)
    have hA : ((b * q + u : ℕ) : R) = (b : R) * (q : R) + (u : R) := by push_cast; ring
    have hB : ((t * q : ℕ) : R) - ((b * q + u : ℕ) : R) =
        ((t : R) - (b : R)) * (q : R) - (u : R) := by push_cast; ring
    have key := inv_pair_identity (u : R) (Ring.inverse (u : R)) ((b * q + u : ℕ) : R)
      (Ring.inverse ((b * q + u : ℕ) : R)) (((t * q : ℕ) : R) - ((b * q + u : ℕ) : R))
      (Ring.inverse (((t * q : ℕ) : R) - ((b * q + u : ℕ) : R)))
      ((b : R) * (q : R)) (((t : R) - (b : R)) * (q : R)) h1 h2 h3 hA hB
    linear_combination key
  rw [Finset.sum_congr rfl pointwise]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.mul_sum]

private lemma G1_blocks {R : Type*} [CommRing R] {p q : ℕ}
    (hR : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → IsUnit (z : R)) (hpq : p ∣ q) (t : ℕ) :
    ∃ g : R, ∑ i ∈ Iset p (t * q),
        Ring.inverse (i : R) * Ring.inverse (((t * q : ℕ) : R) - (i : R)) =
      -(t : R) * (∑ u ∈ Iset p q, Ring.inverse (u : R) ^ 2 +
        (q : R) * ∑ u ∈ Iset p q, Ring.inverse (u : R) ^ 3) + (q : R) ^ 2 * g := by
  choose g hg using fun b => G1_inner hR hpq t b
  have key : ∀ n : ℕ, ∑ b ∈ Finset.range n, ∑ u ∈ Iset p q,
        Ring.inverse ((b * q + u : ℕ) : R) *
          Ring.inverse (((t * q : ℕ) : R) - ((b * q + u : ℕ) : R)) =
      -(n : R) * (∑ u ∈ Iset p q, Ring.inverse (u : R) ^ 2) -
        (q : R) * (∑ u ∈ Iset p q, Ring.inverse (u : R) ^ 3) *
          ((n : R) * (t : R) - (n : R) ^ 2 + (n : R)) +
        (q : R) ^ 2 * ∑ b ∈ Finset.range n, g b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hg n]
      push_cast
      ring
  refine ⟨∑ b ∈ Finset.range t, g b, ?_⟩
  rw [sum_blocks hpq (fun i => Ring.inverse (i : R) *
    Ring.inverse (((t * q : ℕ) : R) - (i : R))) t]
  refine (key t).trans ?_
  ring

/-- Core: `V² = U² (1 + N q² (-t² σ + p h))` for `k = t q`, `q = p q'`, `N = p q n'`. -/
private lemma core {R : Type*} [CommRing R] {p : ℕ}
    (hR : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → IsUnit (z : R)) (q q' n' t : ℕ) (hq : q = p * q') (σ : R)
    (hσ : (∑ u ∈ Iset p q, Ring.inverse (u : R) ^ 2) +
      (q : R) * (∑ u ∈ Iset p q, Ring.inverse (u : R) ^ 3) = (q : R) * σ) :
    ∃ h : R,
      (∏ i ∈ Iset p (t * q), (((p * q * n' : ℕ) : R) + (i : R))) ^ 2 =
      (∏ i ∈ Iset p (t * q), (i : R)) ^ 2 *
        (1 + ((p * q * n' : ℕ) : R) * (q : R) ^ 2 * (-(t : R) ^ 2 * σ + (p : R) * h)) := by
  have hpq : p ∣ q := ⟨q', hq⟩
  have hpk : p ∣ t * q := Dvd.dvd.mul_left hpq t
  obtain ⟨g, hg⟩ := G1_blocks hR hpq t
  obtain ⟨d, hd⟩ := prod_one_add_expand (Iset p (t * q))
    (((p * q * n' : ℕ) : R) * (((p * q * n' : ℕ) : R) + ((t * q : ℕ) : R)))
    (fun i => Ring.inverse (i : R) * Ring.inverse (((t * q : ℕ) : R) - (i : R)))
  rw [pair_prod hR hpk (p * q * n'), hd, hg, hσ]
  refine ⟨-((n' : R) * (t : R) * σ) + ((p : R) * (n' : R) + (t : R)) * (q' : R) * g +
    (q : R) * (n' : R) * ((p : R) * (n' : R) + (t : R)) ^ 2 * d, ?_⟩
  have hqR : (q : R) = (p : R) * (q' : R) := by rw [hq]; push_cast; ring
  push_cast
  rw [hqR]
  ring

/-! The ratio of the two binomial coefficients -/

private lemma isUnit_prod_Iset {R : Type*} [CommRing R] {p : ℕ}
    (hR : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → IsUnit (z : R)) (k : ℕ) :
    IsUnit (∏ i ∈ Iset p k, (i : R)) :=
  Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one
    (fun _ hi => isUnit_nat_of_int hR (mem_Iset.mp hi).2)

private lemma sq_cancel {R : Type*} [CommRing R] (U V BN BM X : R) (hU : IsUnit U)
    (h3 : U * BN = V * BM) (hh : V ^ 2 = U ^ 2 * (1 + X)) : BN ^ 2 = BM ^ 2 * (1 + X) := by
  have h : U ^ 2 * BN ^ 2 = U ^ 2 * (BM ^ 2 * (1 + X)) := by
    linear_combination (U * BN + V * BM) * h3 + BM ^ 2 * hh
  exact (hU.pow 2).mul_left_cancel h

/-- `C(N-1+k, k)² = C(M-1+j, j)² (1 + N q² (-t² σ + p h))` for `N = p M`, `k = p j = t q`. -/
private lemma ratio {R : Type*} [CommRing R] {p : ℕ}
    (hR : ∀ z : ℤ, ¬ (p : ℤ) ∣ z → IsUnit (z : R)) (hp : 0 < p)
    (N M j k q q' n' t BN BM : ℕ) (σ : R)
    (hNM : N = p * M) (hM : 1 ≤ M) (hkj : k = p * j) (hkt : k = t * q) (hq : q = p * q')
    (hN : N = p * q * n')
    (hσ : (∑ u ∈ Iset p q, Ring.inverse (u : R) ^ 2) +
      (q : R) * (∑ u ∈ Iset p q, Ring.inverse (u : R) ^ 3) = (q : R) * σ)
    (hBN : BN = (N - 1 + k).choose k) (hBM : BM = (M - 1 + j).choose j) :
    ∃ h : R, (BN : R) ^ 2 =
      (BM : R) ^ 2 * (1 + (N : R) * (q : R) ^ 2 * (-(t : R) ^ 2 * σ + (p : R) * h)) := by
  subst hkt hN hBN hBM
  obtain ⟨h, hh⟩ := core hR q q' n' t hq σ hσ
  refine ⟨h, ?_⟩
  have h3 : (∏ i ∈ Iset p (t * q), (i : R)) *
      (((p * q * n' - 1 + t * q).choose (t * q) : ℕ) : R) =
      (∏ i ∈ Iset p (t * q), (((p * q * n' : ℕ) : R) + (i : R))) *
        (((M - 1 + j).choose j : ℕ) : R) := by
    have h0 := choose_units_relation (p := p) (M := M) (j := j) hp hM
    rw [← hkj, ← hNM] at h0
    have h1 := congrArg (Nat.cast : ℕ → R) h0
    push_cast at h1 ⊢
    exact h1
  exact sq_cancel _ _ _ _ _ (isUnit_prod_Iset hR (t * q)) h3 hh

/-! Concrete facts in `ℤ_p` and `ZMod p` -/

private lemma exists_sigma {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (m : ℕ) (hm : 1 ≤ m) :
    ∃ σ : PadicInt p, (∑ u ∈ Iset p (p ^ m), Ring.inverse (u : PadicInt p) ^ 2) +
      ((p ^ m : ℕ) : PadicInt p) * (∑ u ∈ Iset p (p ^ m), Ring.inverse (u : PadicInt p) ^ 3) =
      ((p ^ m : ℕ) : PadicInt p) * σ := by
  obtain ⟨s, hs⟩ := S2_dvd hp5 m hm
  refine ⟨s + ∑ u ∈ Iset p (p ^ m), Ring.inverse (u : PadicInt p) ^ 3, ?_⟩
  rw [hs]
  push_cast
  ring

private lemma sum_range_zmod {A : Type*} [AddCommMonoid A] (n : ℕ) [NeZero n] (g : ZMod n → A) :
    ∑ u ∈ Finset.range n, g ((u : ℕ) : ZMod n) = ∑ x : ZMod n, g x := by
  refine Finset.sum_nbij' (fun u => ((u : ℕ) : ZMod n)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro u _; exact Finset.mem_univ _
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro u hu; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hu)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro u _; rfl

private lemma sum_inv_sq_range {p : ℕ} [hpF : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ c ∈ Finset.range p, (((c : ℕ) : ZMod p)⁻¹) ^ 2 = 0 := by
  have hp := hpF.out
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [sum_range_zmod p (fun x => (x⁻¹) ^ 2)]
  have h2 : IsUnit (2 : ZMod p) := by
    have h : IsUnit ((2 : ℕ) : ZMod p) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
    simpa using h
  have h3 : IsUnit (3 : ZMod p) := by
    have h : IsUnit ((3 : ℕ) : ZMod p) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
    simpa using h
  have h := sum_inverse_sq_zmod p h2 h3
  simp only [Ring.inverse_eq_inv] at h
  exact h

/-! Part A: the terms with `p ∤ k` -/

private lemma partA {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) :
    p ^ (3 * r + 3) ∣ ∑ k ∈ Iset p (p ^ r), ((p ^ r - 1 + k).choose k) ^ 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have hN1 : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp.pos
  have hterm : ∀ k ∈ Iset p (p ^ r), ∃ c : ℕ, (p ^ r - 1 + k).choose k = p ^ r * c ∧
      ((k : ZMod p) * (c : ZMod p) = 1) := by
    intro k hk
    rw [mem_Iset] at hk
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (fun h => hk.2 (h ▸ dvd_zero p))
    have hmc := mul_choose_eq hN1 hk1
    have hcop : Nat.Coprime (p ^ r) k :=
      Nat.Coprime.pow_left r (hp.coprime_iff_not_dvd.mpr hk.2)
    have hdvd : p ^ r ∣ (p ^ r - 1 + k).choose k :=
      hcop.dvd_of_dvd_mul_left ⟨_, hmc⟩
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c, hc, ?_⟩
    have h2 : k * c = (p ^ r + (k - 1)).choose (k - 1) := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos r)
      rw [← hmc, hc]
      ring
    have h3 := choose_pow_add_modp (m := r) (n := k - 1) hp (by omega)
    rw [← h2] at h3
    push_cast at h3
    exact h3
  choose! c hc1 hc2 using hterm
  have hsum : ∑ k ∈ Iset p (p ^ r), ((p ^ r - 1 + k).choose k) ^ 4 =
      (p ^ r) ^ 4 * ∑ k ∈ Iset p (p ^ r), (c k) ^ 4 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hc1 k hk, mul_pow]
  have hp_dvd : p ∣ ∑ k ∈ Iset p (p ^ r), (c k) ^ 4 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    have h1 : ∑ k ∈ Iset p (p ^ r), ((c k : ℕ) : ZMod p) ^ 4 =
        ∑ k ∈ Iset p (p ^ r), (((k : ℕ) : ZMod p)⁻¹) ^ 4 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [eq_inv_of_mul_eq_one_right (hc2 k hk)]
    rw [h1]
    have hpr : p ^ r = p ^ (r - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpr, sum_blocks (dvd_refl p) (fun i => (((i : ℕ) : ZMod p)⁻¹) ^ 4) (p ^ (r - 1))]
    have h2 : ∀ b ∈ Finset.range (p ^ (r - 1)),
        ∑ u ∈ Iset p p, ((((b * p + u : ℕ)) : ZMod p)⁻¹) ^ 4 =
          ∑ u ∈ Iset p p, (((u : ℕ) : ZMod p)⁻¹) ^ 4 := by
      intro b _
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega), zero_mul]
  rw [hsum]
  obtain ⟨e, he⟩ := hp_dvd
  rw [he]
  have h4 : p ^ (3 * r + 3) ∣ p ^ (4 * r + 1) := pow_dvd_pow p (by omega)
  exact h4.trans ⟨e, by ring⟩

/-! Interior terms `k = p j` with `p^(r-2) ∤ j` -/

private lemma interior {p r j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hj1 : 1 ≤ j)
    (hnd : ¬ p ^ (r - 2) ∣ j) :
    (p : ℤ) ^ (3 * r + 3) ∣ ((p ^ r - 1 + p * j).choose (p * j) : ℤ) ^ 4 -
      ((p ^ (r - 1) - 1 + j).choose j : ℤ) ^ 4 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, t, ht, hjst⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := j) (by omega) p hp.ne_one
  have hs : s + 3 ≤ r := by
    by_contra hcon
    apply hnd
    rw [hjst]
    exact Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) t
  obtain ⟨d, rfl⟩ : ∃ d, r = s + 3 + d := ⟨r - s - 3, by omega⟩
  have e1 : s + 3 + d - 1 = s + 2 + d := by omega
  rw [e1]
  subst hjst
  obtain ⟨σ, hσ⟩ := exists_sigma (p := p) hp5 (s + 1) (by omega)
  have hM1 : 1 ≤ p ^ (s + 2 + d) := Nat.one_le_pow _ _ hp.pos
  obtain ⟨h, hh⟩ := ratio (R := PadicInt p) (fun z hz => isUnit_intCast_padic hz) hp.pos
    (p ^ (s + 3 + d)) (p ^ (s + 2 + d)) (p ^ s * t) (p * (p ^ s * t)) (p ^ (s + 1)) (p ^ s)
    (p ^ (d + 1)) t
    ((p ^ (s + 3 + d) - 1 + p * (p ^ s * t)).choose (p * (p ^ s * t)))
    ((p ^ (s + 2 + d) - 1 + p ^ s * t).choose (p ^ s * t)) σ
    (by ring) hM1 rfl (by ring) (by ring) (by ring) hσ rfl rfl
  -- valuation of the lower binomial
  have hBMdvd : p ^ (d + 2) ∣ (p ^ (s + 2 + d) - 1 + p ^ s * t).choose (p ^ s * t) := by
    have hmc := mul_choose_eq hM1 hj1
    have h1 : t * (p ^ (s + 2 + d) - 1 + p ^ s * t).choose (p ^ s * t) =
        p ^ (d + 2) * (p ^ (s + 2 + d) + (p ^ s * t - 1)).choose (p ^ s * t - 1) := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos s)
      calc p ^ s * (t * (p ^ (s + 2 + d) - 1 + p ^ s * t).choose (p ^ s * t))
          = p ^ s * t * (p ^ (s + 2 + d) - 1 + p ^ s * t).choose (p ^ s * t) := by ring
        _ = p ^ (s + 2 + d) * (p ^ (s + 2 + d) + (p ^ s * t - 1)).choose (p ^ s * t - 1) := hmc
        _ = p ^ s * (p ^ (d + 2) *
              (p ^ (s + 2 + d) + (p ^ s * t - 1)).choose (p ^ s * t - 1)) := by ring
    have hcop : Nat.Coprime (p ^ (d + 2)) t :=
      Nat.Coprime.pow_left (d + 2) (hp.coprime_iff_not_dvd.mpr ht)
    exact hcop.dvd_of_dvd_mul_left ⟨_, h1⟩
  obtain ⟨w, hw⟩ := hBMdvd
  have hBMR : (((p ^ (s + 2 + d) - 1 + p ^ s * t).choose (p ^ s * t) : ℕ) : PadicInt p) =
      (p : PadicInt p) ^ (d + 2) * (w : PadicInt p) := by
    rw [hw, Nat.cast_mul, Nat.cast_pow]
  rw [← PadicInt.pow_p_dvd_int_iff]
  push_cast
  rw [hBMR] at hh ⊢
  push_cast at hh
  generalize (((p ^ (s + 3 + d) - 1 + p * (p ^ s * t)).choose (p * (p ^ s * t)) : ℕ) :
    PadicInt p) = BN at hh ⊢
  refine ⟨(p : PadicInt p) ^ (2 * d + 1) * (w : PadicInt p) ^ 4 *
    (-(t : PadicInt p) ^ 2 * σ + (p : PadicInt p) * h) *
    (2 + (p : PadicInt p) ^ (s + 3 + d) * ((p : PadicInt p) ^ (s + 1)) ^ 2 *
      (-(t : PadicInt p) ^ 2 * σ + (p : PadicInt p) * h)), ?_⟩
  linear_combination (BN ^ 2 + ((p : PadicInt p) ^ (d + 2) * (w : PadicInt p)) ^ 2 *
    (1 + (p : PadicInt p) ^ (s + 3 + d) * ((p : PadicInt p) ^ (s + 1)) ^ 2 *
      (-(t : PadicInt p) ^ 2 * σ + (p : PadicInt p) * h))) * hh

/-! Top layer `j = p^(r-2) c`, `1 ≤ c < p` -/

private lemma top_term {p ρ c : ℕ} [hpF : Fact p.Prime] (σ : PadicInt p)
    (hσ : (∑ u ∈ Iset p (p ^ (ρ + 1)), Ring.inverse (u : PadicInt p) ^ 2) +
      ((p ^ (ρ + 1) : ℕ) : PadicInt p) *
        (∑ u ∈ Iset p (p ^ (ρ + 1)), Ring.inverse (u : PadicInt p) ^ 3) =
      ((p ^ (ρ + 1) : ℕ) : PadicInt p) * σ)
    (hc1 : 1 ≤ c) (hcp : c < p) :
    ∃ β : ℕ, (c : ZMod p) * (β : ZMod p) = 1 ∧
      (p : PadicInt p) ^ (3 * (ρ + 2) + 3) ∣
        (((p ^ (ρ + 2) - 1 + p * (p ^ ρ * c)).choose (p * (p ^ ρ * c)) : ℕ) : PadicInt p) ^ 4 -
        (((p ^ (ρ + 1) - 1 + p ^ ρ * c).choose (p ^ ρ * c) : ℕ) : PadicInt p) ^ 4 +
        (p : PadicInt p) ^ (3 * (ρ + 2) + 2) *
          (2 * σ * ((c : PadicInt p) ^ 2 * (β : PadicInt p) ^ 4)) := by
  have hp := hpF.out
  have hM1 : 1 ≤ p ^ (ρ + 1) := Nat.one_le_pow _ _ hp.pos
  have hj1 : 1 ≤ p ^ ρ * c := Nat.mul_pos (pow_pos hp.pos ρ) hc1
  have hmc := mul_choose_eq hM1 hj1
  have h1 : c * (p ^ (ρ + 1) - 1 + p ^ ρ * c).choose (p ^ ρ * c) =
      p * (p ^ (ρ + 1) + (p ^ ρ * c - 1)).choose (p ^ ρ * c - 1) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos ρ)
    calc p ^ ρ * (c * (p ^ (ρ + 1) - 1 + p ^ ρ * c).choose (p ^ ρ * c))
        = p ^ ρ * c * (p ^ (ρ + 1) - 1 + p ^ ρ * c).choose (p ^ ρ * c) := by ring
      _ = p ^ (ρ + 1) * (p ^ (ρ + 1) + (p ^ ρ * c - 1)).choose (p ^ ρ * c - 1) := hmc
      _ = p ^ ρ * (p * (p ^ (ρ + 1) + (p ^ ρ * c - 1)).choose (p ^ ρ * c - 1)) := by ring
  have hcop : Nat.Coprime p c :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hc1 hcp)
  have hdvd : p ∣ (p ^ (ρ + 1) - 1 + p ^ ρ * c).choose (p ^ ρ * c) :=
    hcop.dvd_of_dvd_mul_left ⟨_, h1⟩
  obtain ⟨β, hβ⟩ := hdvd
  have h2 : c * β = (p ^ (ρ + 1) + (p ^ ρ * c - 1)).choose (p ^ ρ * c - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    rw [← h1, hβ]
    ring
  have hlt : p ^ ρ * c < p ^ (ρ + 1) := by
    rw [pow_succ]
    exact Nat.mul_lt_mul_of_pos_left hcp (pow_pos hp.pos ρ)
  have hΓ := choose_pow_add_modp (m := ρ + 1) (n := p ^ ρ * c - 1) hp (by omega)
  refine ⟨β, ?_, ?_⟩
  · rw [← h2] at hΓ
    push_cast at hΓ
    exact hΓ
  · obtain ⟨h, hh⟩ := ratio (R := PadicInt p) (fun z hz => isUnit_intCast_padic hz) hp.pos
      (p ^ (ρ + 2)) (p ^ (ρ + 1)) (p ^ ρ * c) (p * (p ^ ρ * c)) (p ^ (ρ + 1)) (p ^ ρ) 1 c
      ((p ^ (ρ + 2) - 1 + p * (p ^ ρ * c)).choose (p * (p ^ ρ * c)))
      ((p ^ (ρ + 1) - 1 + p ^ ρ * c).choose (p ^ ρ * c)) σ
      (by ring) hM1 rfl (by ring) (by ring) (by ring) hσ rfl rfl
    have hBMR : (((p ^ (ρ + 1) - 1 + p ^ ρ * c).choose (p ^ ρ * c) : ℕ) : PadicInt p) =
        (p : PadicInt p) * (β : PadicInt p) := by
      rw [hβ, Nat.cast_mul]
    rw [hBMR] at hh ⊢
    push_cast at hh
    generalize (((p ^ (ρ + 2) - 1 + p * (p ^ ρ * c)).choose (p * (p ^ ρ * c)) : ℕ) :
      PadicInt p) = BN at hh ⊢
    refine ⟨(β : PadicInt p) ^ 4 * (2 * h + (p : PadicInt p) ^ (3 * ρ + 3) *
      (-(c : PadicInt p) ^ 2 * σ + (p : PadicInt p) * h) ^ 2), ?_⟩
    linear_combination (BN ^ 2 + ((p : PadicInt p) * (β : PadicInt p)) ^ 2 *
      (1 + (p : PadicInt p) ^ (ρ + 2) * ((p : PadicInt p) ^ (ρ + 1)) ^ 2 *
        (-(c : PadicInt p) ^ 2 * σ + (p : PadicInt p) * h))) * hh

private lemma top_layer {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    (p : ℤ) ^ (3 * r + 3) ∣ ∑ c ∈ Finset.range p,
      (((p ^ r - 1 + p * (p ^ (r - 2) * c)).choose (p * (p ^ (r - 2) * c)) : ℤ) ^ 4 -
        ((p ^ (r - 1) - 1 + p ^ (r - 2) * c).choose (p ^ (r - 2) * c) : ℤ) ^ 4) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ρ, rfl⟩ : ∃ ρ, r = ρ + 2 := ⟨r - 2, by omega⟩
  have e1 : ρ + 2 - 2 = ρ := by omega
  have e2 : ρ + 2 - 1 = ρ + 1 := by omega
  rw [e1, e2]
  obtain ⟨σ, hσ⟩ := exists_sigma (p := p) hp5 (ρ + 1) (by omega)
  have hterm : ∀ c ∈ Finset.range p, ∃ β : ℕ,
      ((c : ZMod p) ^ 2 * (β : ZMod p) ^ 4 = (((c : ℕ) : ZMod p)⁻¹) ^ 2) ∧
      (p : PadicInt p) ^ (3 * (ρ + 2) + 3) ∣
        (((p ^ (ρ + 2) - 1 + p * (p ^ ρ * c)).choose (p * (p ^ ρ * c)) : ℕ) : PadicInt p) ^ 4 -
        (((p ^ (ρ + 1) - 1 + p ^ ρ * c).choose (p ^ ρ * c) : ℕ) : PadicInt p) ^ 4 +
        (p : PadicInt p) ^ (3 * (ρ + 2) + 2) *
          (2 * σ * ((c : PadicInt p) ^ 2 * (β : PadicInt p) ^ 4)) := by
    intro c hc
    rcases Nat.eq_zero_or_pos c with rfl | hc1
    · refine ⟨0, by simp, ?_⟩
      simp
    · obtain ⟨β, hβ1, hβ2⟩ := top_term (ρ := ρ) σ hσ hc1 (Finset.mem_range.mp hc)
      refine ⟨β, ?_, hβ2⟩
      have hb : (β : ZMod p) = ((c : ℕ) : ZMod p)⁻¹ := eq_inv_of_mul_eq_one_right hβ1
      calc (c : ZMod p) ^ 2 * (β : ZMod p) ^ 4
          = ((c : ZMod p) * (β : ZMod p)) ^ 2 * (β : ZMod p) ^ 2 := by ring
        _ = (β : ZMod p) ^ 2 := by rw [hβ1, one_pow, one_mul]
        _ = (((c : ℕ) : ZMod p)⁻¹) ^ 2 := by rw [hb]
  choose! β hβ1 hβ2 using hterm
  have hsumdvd := Finset.dvd_sum (fun c hc => hβ2 c hc)
  have hpd : p ∣ ∑ c ∈ Finset.range p, c ^ 2 * (β c) ^ 4 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [Finset.sum_congr rfl hβ1]
    exact sum_inv_sq_range hp5
  obtain ⟨w, hw⟩ := hpd
  have hw' : ∑ c ∈ Finset.range p, (c : PadicInt p) ^ 2 * (β c : PadicInt p) ^ 4 =
      (p : PadicInt p) * (w : PadicInt p) := by
    have h := congrArg (Nat.cast : ℕ → PadicInt p) hw
    push_cast at h
    exact h
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw'] at hsumdvd
  have h2 : (p : PadicInt p) ^ (3 * (ρ + 2) + 3) ∣ (p : PadicInt p) ^ (3 * (ρ + 2) + 2) *
      (2 * σ * ((p : PadicInt p) * (w : PadicInt p))) := ⟨2 * σ * w, by ring⟩
  have h3 := (dvd_add_left h2).mp hsumdvd
  rw [← PadicInt.pow_p_dvd_int_iff]
  push_cast
  exact h3

private theorem main_thm (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    ((p : ℤ) ^ (3 * r + 3)) ∣ ((OMA.S_oeis_a219562.a (p ^ r - 1) : ℤ) -
      (OMA.S_oeis_a219562.a (p ^ (r - 1) - 1) : ℤ)) := by
  have hN1 : 1 ≤ p ^ r := Nat.one_le_pow _ _ hp.pos
  have hM1 : 1 ≤ p ^ (r - 1) := Nat.one_le_pow _ _ hp.pos
  have hNM : p ^ r = p * p ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hMe : p ^ (r - 1) = p ^ (r - 2) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have ha1 : (OMA.S_oeis_a219562.a (p ^ r - 1) : ℤ) =
      ∑ k ∈ Iset p (p ^ r), ((p ^ r - 1 + k).choose k : ℤ) ^ 4 +
        ∑ l ∈ Finset.range (p ^ (r - 1)), ((p ^ r - 1 + p * l).choose (p * l) : ℤ) ^ 4 := by
    unfold OMA.S_oeis_a219562.a
    rw [Nat.sub_add_cancel hN1, Nat.cast_sum]
    simp only [Nat.cast_pow]
    exact sum_range_split' p (p ^ (r - 1)) (p ^ r) hp.pos hNM _
  have ha2 : (OMA.S_oeis_a219562.a (p ^ (r - 1) - 1) : ℤ) =
      ∑ l ∈ Finset.range (p ^ (r - 1)), ((p ^ (r - 1) - 1 + l).choose l : ℤ) ^ 4 := by
    unfold OMA.S_oeis_a219562.a
    rw [Nat.sub_add_cancel hM1, Nat.cast_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Nat.cast_pow]
  rw [ha1, ha2, add_sub_assoc, ← Finset.sum_sub_distrib]
  apply dvd_add
  · have h := Int.natCast_dvd_natCast.mpr (partA hp hr)
    push_cast at h
    exact h
  · rw [sum_range_split' (p ^ (r - 2)) p (p ^ (r - 1)) (pow_pos hp.pos _) hMe]
    apply dvd_add
    · apply Finset.dvd_sum
      intro l hl
      rw [Finset.mem_filter] at hl
      have hl1 : 1 ≤ l := Nat.pos_of_ne_zero (fun h => hl.2 (h ▸ dvd_zero _))
      exact interior hp hp5 hl1 hl.2
    · exact top_layer hp hp5 hr

end A219562H2

theorem OMA.solution : type_of% @OMA.S_oeis_a219562.main := by
  refine ⟨?_, ?_⟩
  · intro p hp hp7
    have h := SolvedConjecture10.conjecture_1 p hp hp7
    have e : OMA.S_oeis_a219562.a = SolvedConjecture10.a := rfl
    have h1 : 1 ≤ SolvedConjecture10.a (p - 1) := by
      unfold SolvedConjecture10.a
      calc 1 = ((p - 1 + 0).choose 0) ^ 4 := by simp
        _ ≤ ∑ k ∈ Finset.range (p - 1 + 1), ((p - 1 + k).choose k) ^ 4 :=
            Finset.single_le_sum (f := fun k => ((p - 1 + k).choose k) ^ 4)
              (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.succ_pos _))
    rw [e]
    exact ((Nat.modEq_iff_dvd' h1).mpr h).symm
  · intro p r hp hp5 hr
    have h := A219562H2.main_thm p r hp hp5 hr
    rw [Nat.modEq_iff_dvd]
    have h' := (dvd_sub_comm).mp h
    exact_mod_cast h'
