import OMAReductions.R_Erdos848_erdos_848_R1_H2_R1_H2_R1_H3_R1
import Mathlib

/-!
# Proof of `Erdos848.erdos_848.R1.H2.R1.H2.R1.H3.R1.H1`

Bounded prime-factor support regime (`160000000 ≤ N < 1500000000`) for Cases II and III.1
of Erdős Problem 848 (Sawicki 2025):

1. **Unitary divisor keys & root-class spacing (`large_primes_any`):** Adapts the Apache-2.0
   unitary-divisor and root-class framework of `@Deldor14` (PR #8925 / `Erdos848...R1.H1.lean`)
   and Alex Chengyu Li. For ANY `b ∈ [1, N]` (`160M ≤ N < 1.5B`), primes `p > N / 48` with
   `p^2 ∣ a*b + 1` yield `d = (a*b + 1)/p^2 < 2304` and at most `1 + 47 / d` solutions per
   `(d, root_class)`. Together with `b < 1.5 × 10^9` (`prod_s * tail_prod ≤ 1.5 × 10^9`) and
   a certified quadratic-residue tree over `{2, 3, 5, 7, 11, 13, 17, 19, 23}`, this uniformly
   bounds the large-prime count by `161792`.
2. **Prime counting via `Chebyshev.theta` (`prime_count_div`):** Two-step Chebyshev bound
   `17 * π(N / K) ≤ 2 * (N / K) + 17 * 25880` for `K = 48` and `K = 150`.
3. **Diagonal sieve (`vCount_tail` & `diagonal_gap`):** For `a^2 + 1` non-squarefree with
   `IsStar a`, only primes `p ≡ 1 (mod 4), p ≥ 13` contribute; for `p > N / 150`, dyadic
   `diagonal_gap` (`d < 22500`, `d % 4 ∈ {1, 2}`, `d % 3 ≠ 0`) gives at most `60000` solutions.
4. **Part 1 & Part 2 assembly:** Splitting `p = 13` and `p = 17` in `lemCCount b` and sharing
   the `p > √N` bound across `badCount` and `lemC_13, lemC_17` yields total density `< 0.0392 N < c7`
   in Part 1 and `< 0.0355 N < c7` in Part 2.
-/

open scoped BigOperators Finset Nat.Prime

namespace OMA.P_Erdos848_H3_R1_H1

open Finset

/-! ### Section 1: Unitary Divisor Keys and Root Classes -/

private theorem coprime_factor_ext {a c a' c' : ℕ}
    (pos : 0 < a * c) (eq : a * c = a' * c') (ha : a.Coprime c) (ha' : a'.Coprime c')
    (hs : a.primeFactors = a'.primeFactors) : a = a' := by
  have pos' : 0 < a' * c' := eq ▸ pos
  have ac := Nat.pos_of_mul_pos_right pos
  have av := Nat.pos_of_mul_pos_left pos
  have ac' := Nat.pos_of_mul_pos_right pos'
  have av' := Nat.pos_of_mul_pos_left pos'
  have h : a.Coprime c' := (Nat.disjoint_primeFactors (by positivity) (by positivity)).mp
    (hs ▸ ha'.disjoint_primeFactors)
  have h' : a'.Coprime c := (Nat.disjoint_primeFactors (by positivity) (by positivity)).mp
    (hs ▸ ha.disjoint_primeFactors)
  apply Nat.dvd_antisymm
  · exact h.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right a c)
  · exact h'.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right a' c')

private theorem count_unitary_keys (b : ℕ) (bpos : 0 < b) :
    (b.divisors.filter (fun g => (Nat.gcd g (b / g)) ∣ 2)).card ≤ 2 * 2 ^ b.primeFactors.card := by
  classical
  let k (g : ℕ) := Nat.gcd g (b / g)
  let a (g : ℕ) := g / k g
  let c (g : ℕ) := (b / g) / k g
  let D := b.divisors.filter (fun g => k g ∣ 2)
  let K := (Finset.Icc 1 2) ×ˢ b.primeFactors.powerset
  let code (g : ℕ) := (k g, (a g).primeFactors)
  have gd {g : ℕ} (hg : g ∈ D) : g ∣ b := (Nat.mem_divisors.mp (Finset.mem_filter.mp hg).1).1
  have kg {g : ℕ} (hg : g ∈ D) : 0 < k g :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (gd hg) bpos)
  have ag (g : ℕ) : a g * k g = g := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have cg (g : ℕ) : c g * k g = b / g := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have B {g : ℕ} (hg : g ∈ D) : (a g * c g) * (k g * k g) = b := calc
    _ = (a g * k g) * (c g * k g) := by ring
    _ = b := by rw [ag, cg, Nat.mul_div_cancel' (gd hg)]
  have count : D.card ≤ K.card := by
    apply Finset.card_le_card_of_injOn code
    · intro g hg
      refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨kg hg, ?_⟩, Finset.mem_powerset.mpr ?_⟩
      · exact Nat.le_of_dvd (by decide) (Finset.mem_filter.mp hg).2
      · exact Nat.primeFactors_mono ((Nat.div_dvd_of_dvd (Nat.gcd_dvd_left ..)).trans (gd hg)) bpos.ne'
    · intro x hx y hy he
      have hk : k x = k y := congrArg Prod.fst he
      have hs : (a x).primeFactors = (a y).primeFactors := congrArg Prod.snd he
      have e : a x * c x = a y * c y := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (kg hx) (kg hx))
        rw [B hx, hk, B hy]
      have pp : 0 < a x * c x :=
        Nat.pos_of_mul_pos_right (show 0 < (a x * c x) * (k x * k x) by rw [B hx]; exact bpos)
      have ax := coprime_factor_ext pp e (Nat.coprime_div_gcd_div_gcd (kg hx))
        (Nat.coprime_div_gcd_div_gcd (kg hy)) hs
      rw [← ag x, ← ag y, ax, hk]
  simpa [K, Finset.card_product] using count

private theorem root_factor {B D R X T U : ℤ}
    (hr : D * R ^ 2 = B * T + 1) (hx : D * X ^ 2 = B * U + 1) : B ∣ (X - R) * (X + R) := by
  refine ⟨R ^ 2 * U - X ^ 2 * T, ?_⟩
  linear_combination R ^ 2 * hx - X ^ 2 * hr

private theorem gcd_times_sum {B R X : ℤ} (hx : B ∣ (X - R) * (X + R)) :
    B ∣ (Int.gcd B (X - R) : ℤ) * (X + R) := by
  obtain ⟨q, hq⟩ := hx
  refine ⟨Int.gcdA B (X - R) * (X + R) + Int.gcdB B (X - R) * q, ?_⟩
  rw [Int.gcd_eq_gcd_ab]
  linear_combination Int.gcdB B (X - R) * hq

private theorem roots_in_class {B D R X Y T U V : ℤ}
    (hr : D * R ^ 2 = B * T + 1) (hx : D * X ^ 2 = B * U + 1) (hy : D * Y ^ 2 = B * V + 1)
    (hg : Int.gcd B (X - R) = Int.gcd B (Y - R)) : B ∣ 2 * (Y - X) := by
  let g : ℤ := Int.gcd B (X - R)
  have h₁ : B ∣ g * (X + R) := gcd_times_sum (root_factor hr hx)
  have h₂ : B ∣ g * (Y + R) := by simpa only [g, hg] using gcd_times_sum (root_factor hr hy)
  have h₃ : B ∣ g * (Y - X) := by convert! dvd_sub h₂ h₁ using 1; ring
  have gx : g ∣ X - R := Int.gcd_dvd_right ..
  have gy : g ∣ Y - R := by simpa only [g, hg] using Int.gcd_dvd_right B (Y - R)
  have gxy : g ∣ Y - X := by convert! dvd_sub gy gx using 1; ring
  have plus : B ∣ (Y - X) * (X + R) := h₁.trans (mul_dvd_mul_right gxy _)
  have minus : B ∣ (Y - X) * (X - R) := by
    rw [mul_comm (Y - X) (X - R)]
    exact h₃.trans (mul_dvd_mul_right gx _)
  have twice : B ∣ 2 * R * (Y - X) := by convert! dvd_sub plus minus using 1; ring
  obtain ⟨k, hk⟩ := twice
  refine ⟨D * R * k - 2 * (Y - X) * T, ?_⟩
  linear_combination D * R * hk - 2 * (Y - X) * hr

private theorem root_key_valid {b : ℕ} (bpos : 0 < b) {D R X T U : ℤ}
    (hr : D * R ^ 2 = (b : ℤ) * T + 1) (hx : D * X ^ 2 = (b : ℤ) * U + 1) :
    let g := Int.gcd (b : ℤ) (X - R)
    Nat.gcd g (b / g) ∣ 2 := by
  let g := Int.gcd (b : ℤ) (X - R)
  let h := b / g
  let k := Nat.gcd g h
  change k ∣ 2
  have gb : g ∣ b := by exact_mod_cast Int.gcd_dvd_left (b : ℤ) (X - R)
  have gpos := Nat.pos_of_dvd_of_pos gb bpos
  have gh : (g : ℤ) * (h : ℤ) = (b : ℤ) := by exact_mod_cast Nat.mul_div_cancel' gb
  have gs : (b : ℤ) ∣ (g : ℤ) * (X + R) := gcd_times_sum (root_factor hr hx)
  obtain ⟨q, hq⟩ := gs
  have hs : (h : ℤ) ∣ X + R := by
    refine ⟨q, mul_left_cancel₀ (show (g : ℤ) ≠ 0 by exact_mod_cast gpos.ne') ?_⟩
    rw [← mul_assoc, gh, hq]
  have kg : (k : ℤ) ∣ (g : ℤ) := by exact_mod_cast Nat.gcd_dvd_left g h
  have kh : (k : ℤ) ∣ (h : ℤ) := by exact_mod_cast Nat.gcd_dvd_right g h
  have km : (k : ℤ) ∣ X - R := kg.trans (Int.gcd_dvd_right ..)
  have kp : (k : ℤ) ∣ X + R := kh.trans hs
  have kr := dvd_sub kp km
  rw [show X + R - (X - R) = 2 * R by ring] at kr
  have kb : (k : ℤ) ∣ (b : ℤ) := kg.trans (by exact_mod_cast gb)
  have old : (k : ℤ) ∣ (2 * R) * (D * R) - 2 * ((b : ℤ) * T) :=
    dvd_sub (dvd_mul_of_dvd_left kr _) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left kb _) _)
  have two : (2 : ℤ) = (2 * R) * (D * R) - 2 * ((b : ℤ) * T) := by linear_combination -2 * hr
  rw [← two] at old
  exact_mod_cast old

/-! ### Section 2: General Large-Prime Bound (`p > N / 48`) for `b < 1.5 × 10^9` -/

private lemma card_chain_le_of_step {S : Finset ℕ} {b d K N : ℕ}
    (hb : 0 < b) (hd : 0 < d) (hN : 0 < N)
    (p : ℕ → ℕ)
    (hpinj : Set.InjOn p (S : Set ℕ))
    (hxlt : ∀ x ∈ S, x ≤ N)
    (heq : ∀ x ∈ S, d * (p x) ^ 2 = b * x + 1)
    (hbig : ∀ x ∈ S, N < K * p x)
    (hstep : ∀ x ∈ S, ∀ y ∈ S, p x < p y → b ≤ 2 * (p y - p x)) :
    S.card ≤ 1 + (K - 1) / d := by
  classical
  by_cases hS : S.card ≤ 1
  · exact hS.trans (Nat.le_add_right 1 _)
  · have hne : (S.image p).Nonempty := (Finset.card_pos.mp (by omega)).image p
    let pmin := (S.image p).min' hne
    let pmax := (S.image p).max' hne
    obtain ⟨xmin, hxmin, hpmin⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
    obtain ⟨xmax, hxmax, hpmax⟩ := Finset.mem_image.mp (Finset.max'_mem _ hne)
    have hcard_img : (S.image p).card = S.card := Finset.card_image_of_injOn hpinj
    -- Sort S.image p into a strictly increasing list; consecutive gaps satisfy 2*(q - r) >= b
    let L := (S.image p).sort (· ≤ ·)
    have hL_len : L.length = S.card := by rw [Finset.length_sort, hcard_img]
    have hL_sorted : L.Pairwise (· < ·) :=
      ((Finset.pairwise_sort (S.image p) (· ≤ ·)).and (Finset.sort_nodup (S.image p) (· ≤ ·))).imp
        fun h => lt_of_le_of_ne h.1 h.2
    have hL_mem : ∀ z ∈ L, z ∈ S.image p := fun z hz => (Finset.mem_sort (· ≤ ·)).mp hz
    have hgap_list : ∀ l : List ℕ, l.Pairwise (· < ·) →
        (∀ z ∈ l, z ∈ S.image p) →
        ∀ hne' : l ≠ [],
          (l.length - 1) * b ≤ 2 * (l.getLast hne' - l.head hne') := by
      intro l
      induction l with
      | nil => intro _ _ h; exact (h rfl).elim
      | cons a t ih =>
        intro hs hmem _
        cases t with
        | nil => simp
        | cons c t' =>
          have hlt_ac : a < c := (List.pairwise_cons.mp hs).1 c (List.mem_cons_self ..)
          have ha_mem : a ∈ S.image p := hmem a (List.mem_cons_self ..)
          have hc_mem : c ∈ S.image p := hmem c (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          obtain ⟨xa, hxa, hpa⟩ := Finset.mem_image.mp ha_mem
          obtain ⟨xc, hxc, hpc⟩ := Finset.mem_image.mp hc_mem
          have hstep1 : b ≤ 2 * (c - a) := by
            have := hstep xa hxa xc hxc (by rw [hpa, hpc]; exact hlt_ac)
            rwa [hpa, hpc] at this
          have htail := ih (List.pairwise_cons.mp hs).2
            (fun z hz => hmem z (List.mem_cons_of_mem _ hz)) (List.cons_ne_nil c t')
          have hc_le_last : c ≤ (c :: t').getLast (List.cons_ne_nil c t') := by
            have hmem_last := List.getLast_mem (List.cons_ne_nil c t')
            rcases List.mem_cons.mp hmem_last with h1 | h2
            · exact h1.ge
            · exact ((List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1 _ h2).le
          simp only [List.length_cons, List.head_cons, List.getLast_cons (List.cons_ne_nil c t')] at htail ⊢
          have hmul_b : (t'.length + 1) * b = b + t'.length * b := by ring
          have hac : a ≤ c := hlt_ac.le
          rw [Nat.add_sub_cancel] at htail
          rw [Nat.add_sub_cancel, hmul_b]; omega
    have hL_ne : L ≠ [] := by intro h; rw [h] at hL_len; simp at hL_len; omega
    have hspan := hgap_list L hL_sorted hL_mem hL_ne
    have hhead_ge : pmin ≤ L.head hL_ne := Finset.min'_le _ _ (hL_mem _ (List.head_mem hL_ne))
    have hlast_le : L.getLast hL_ne ≤ pmax := Finset.le_max' _ _ (hL_mem _ (List.getLast_mem hL_ne))
    have hspan2 : (S.card - 1) * b ≤ 2 * (pmax - pmin) := by
      rw [hL_len] at hspan
      omega
    have hpmin_lt_max : pmin < pmax := by
      have hne_eq : pmin ≠ pmax := by
        intro heq_mm
        have : (S.image p).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro u hu v hv
          have h1 := Finset.min'_le _ u hu
          have h2 := Finset.le_max' _ u hu
          have h3 := Finset.min'_le _ v hv
          have h4 := Finset.le_max' _ v hv
          omega
        omega
      exact lt_of_le_of_ne (Finset.min'_le _ _ (Finset.max'_mem _ hne)) hne_eq
    have heq_min := heq xmin hxmin
    have heq_max := heq xmax hxmax
    rw [hpmin] at heq_min
    rw [hpmax] at heq_max
    have hdiff_eq : d * (pmax - pmin) * (pmax + pmin) = b * (xmax - xmin) := by
      have hsq : pmax ^ 2 - pmin ^ 2 = (pmax - pmin) * (pmax + pmin) := by
        zify [hpmin_lt_max.le, Nat.pow_le_pow_left hpmin_lt_max.le 2]; ring
      have h1 : d * (pmax ^ 2 - pmin ^ 2) = b * (xmax - xmin) := by
        have hlt_x : xmin ≤ xmax := by
          have : pmin ^ 2 ≤ pmax ^ 2 := Nat.pow_le_pow_left hpmin_lt_max.le 2
          nlinarith
        zify [hlt_x, Nat.pow_le_pow_left hpmin_lt_max.le 2]
        nlinarith
      rw [Nat.mul_assoc, ← hsq]; exact h1
    have hxmax_le : xmax ≤ N := hxlt xmax hxmax
    have hbx : b * (xmax - xmin) ≤ b * N := Nat.mul_le_mul_left b (by omega)
    have hbig_min : N < K * pmin := by dsimp only [pmin]; rw [← hpmin]; exact hbig xmin hxmin
    have hbig_sum : 2 * N < K * (pmax + pmin) := by nlinarith
    have hd_mul_lt : d * (2 * (pmax - pmin)) * N < K * b * N := by
      have hpos_dp : 0 < d * (pmax - pmin) := Nat.mul_pos hd (by omega)
      calc d * (2 * (pmax - pmin)) * N
          = d * (pmax - pmin) * (2 * N) := by ring
        _ < d * (pmax - pmin) * (K * (pmax + pmin)) := Nat.mul_lt_mul_of_pos_left hbig_sum hpos_dp
        _ = K * (d * (pmax - pmin) * (pmax + pmin)) := by ring
        _ = K * (b * (xmax - xmin)) := by rw [hdiff_eq]
        _ ≤ K * (b * N) := Nat.mul_le_mul_left K hbx
        _ = K * b * N := by ring
    have hd_lt : d * (2 * (pmax - pmin)) < K * b := Nat.lt_of_mul_lt_mul_right hd_mul_lt
    have hd_card_lt : d * (S.card - 1) * b < K * b := calc
      d * (S.card - 1) * b = d * ((S.card - 1) * b) := by ring
      _ ≤ d * (2 * (pmax - pmin)) := Nat.mul_le_mul_left d hspan2
      _ < K * b := hd_lt
    have hfinal : d * (S.card - 1) < K := Nat.lt_of_mul_lt_mul_right hd_card_lt
    have hle_div : S.card - 1 ≤ (K - 1) / d := by
      rw [Nat.le_div_iff_mul_le hd]
      rw [Nat.mul_comm] at hfinal
      omega
    omega

private def qrMask : ℕ → ℕ
  | 2 => 2
  | 3 => 2
  | 5 => 18
  | 7 => 22
  | 11 => 570
  | 13 => 5658
  | 17 => 107286
  | 19 => 199410
  | 23 => 340830
  | _ => 0

private def qr (q d : ℕ) : Bool :=
  (qrMask q).testBit (d % q)

private lemma qr_sound_small {q d p x b : ℕ} (hq_mem : q ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ))
    (hqb : q ∣ b) (heq : d * p ^ 2 = b * x + 1) : qr q d = true := by
  have hmod1 : ((d % q) * (p % q) ^ 2) % q = 1 % q := by
    have h1 : (d * p ^ 2) % q = (b * x + 1) % q := by rw [heq]
    have h2 : (b * x + 1) % q = 1 % q := by
      obtain ⟨k, rfl⟩ := hqb
      rw [Nat.mul_assoc, Nat.mul_add_mod]
    rw [h2, Nat.mul_mod d, Nat.pow_mod p] at h1
    simpa [Nat.mul_mod] using h1
  have hcheck : ∀ q' ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23] : List ℕ),
      ∀ r : Fin q', ∀ u : Fin q', (r.val * u.val ^ 2) % q' = 1 % q' →
        (qrMask q').testBit r.val = true := by decide +kernel
  have hq_list : q ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23] : List ℕ) := by simpa using hq_mem
  have hq_pos : 0 < q := by
    rcases (by simpa using hq_mem : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 11 ∨ q = 13 ∨ q = 17 ∨ q = 19 ∨ q = 23)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact hcheck q hq_list ⟨d % q, Nat.mod_lt _ hq_pos⟩ ⟨p % q, Nat.mod_lt _ hq_pos⟩ hmod1

private def smallPrimesList : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23]
private def smallPrimesSet : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23}

private def maxTailCount (prodS : ℕ) : ℕ :=
  if prodS * 29 ^ 5 ≤ 1500000000 then 5
  else if prodS * 29 ^ 4 ≤ 1500000000 then 4
  else if prodS * 29 ^ 3 ≤ 1500000000 then 3
  else if prodS * 29 ^ 2 ≤ 1500000000 then 2
  else if prodS * 29 ≤ 1500000000 then 1
  else 0

private def walkLarge : List ℕ → List ℕ → ℕ → ℕ → Bool
  | [], good, c, prodS =>
    if 1500000000 < prodS then true
    else
      let w := good.foldl (fun acc d => acc + (if d < 48 then 1 + 47 / d else 1)) 0
      decide (2 * 2 ^ (c + maxTailCount prodS) * w ≤ 161792)
  | q :: l, good, c, prodS =>
    if 1500000000 < prodS then true
    else walkLarge l good c prodS && walkLarge l (good.filter (qr q)) (c + 1) (prodS * q)

private def initDivs48 : List ℕ := (List.range 2304).filter (fun d => decide (1 ≤ d))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
private theorem walkLarge_ok : walkLarge smallPrimesList initDivs48 0 1 = true := by
  decide +kernel

private lemma foldl_add_eq_sum (l : List ℕ) (f : ℕ → ℕ) (init : ℕ) :
    l.foldl (fun acc d => acc + f d) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    omega

private lemma walkLarge_sound (l good : List ℕ) (c prodS : ℕ)
    (h : walkLarge l good c prodS = true)
    (s D : Finset ℕ) (hsub : ∀ q ∈ s, q ∈ l) (hpos_l : ∀ q ∈ l, 0 < q)
    (hprodS : prodS * ∏ q ∈ s, q ≤ 1500000000)
    (hdom : ∀ d ∈ D, d ∈ good) (hnd : good.Nodup)
    (hqr : ∀ d ∈ D, ∀ q ∈ s, qr q d = true) :
    2 * 2 ^ (c + s.card + maxTailCount (prodS * ∏ q ∈ s, q)) *
      (∑ d ∈ D, (1 + 47 / d)) ≤ 161792 := by
  induction l generalizing good c prodS s with
  | nil =>
    have hs : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun q hq => by simpa using hsub q hq
    subst hs
    simp only [Finset.card_empty, Nat.add_zero, Finset.prod_empty, mul_one] at hprodS ⊢
    unfold walkLarge at h
    have hnot : ¬ (1500000000 < prodS) := by omega
    rw [if_neg hnot] at h
    simp only [decide_eq_true_eq] at h
    rw [foldl_add_eq_sum, zero_add] at h
    have hsum_eq : (good.map (fun d => if d < 48 then 1 + 47 / d else 1)) =
        (good.map (fun d => 1 + 47 / d)) :=
      List.map_congr_left fun d _ => by
        split_ifs with h48
        · rfl
        · rw [Nat.div_eq_of_lt (by omega)]
    rw [hsum_eq] at h
    have hsum_le : ∑ d ∈ D, (1 + 47 / d) ≤ (good.map (fun d => 1 + 47 / d)).sum := by
      have hsubD : D ⊆ good.toFinset := fun d hd => List.mem_toFinset.mpr (hdom d hd)
      calc ∑ d ∈ D, (1 + 47 / d)
          ≤ ∑ d ∈ good.toFinset, (1 + 47 / d) := Finset.sum_le_sum_of_subset hsubD
        _ = (good.map (fun d => 1 + 47 / d)).sum := by
            rw [List.sum_toFinset _ hnd]
    exact (Nat.mul_le_mul_left _ hsum_le).trans h
  | cons q l ih =>
    have hnot : ¬ (1500000000 < prodS) := by
      have hpos : 1 ≤ ∏ r ∈ s, r := Finset.prod_pos fun r hr => hpos_l r (hsub r hr)
      nlinarith
    have hpos_tail : ∀ r ∈ l, 0 < r := fun r hr => hpos_l r (List.mem_cons_of_mem _ hr)
    simp only [walkLarge, if_neg hnot, Bool.and_eq_true] at h
    by_cases hq : q ∈ s
    · have hsub' : ∀ r ∈ s.erase q, r ∈ l := fun r hr =>
        (List.mem_cons.mp (hsub r (Finset.mem_of_mem_erase hr))).resolve_left (Finset.ne_of_mem_erase hr)
      have hprod_eq : prodS * ∏ r ∈ s, r = (prodS * q) * ∏ r ∈ s.erase q, r := by
        rw [← Finset.mul_prod_erase s (fun r => r) hq]; ring
      have hcard_eq : c + s.card = (c + 1) + (s.erase q).card := by
        have := Finset.card_erase_add_one hq; omega
      rw [hprod_eq, hcard_eq]
      exact ih (good.filter (qr q)) (c + 1) (prodS * q) h.2 (s.erase q) hsub' hpos_tail
        (hprod_eq ▸ hprodS)
        (fun d hd => List.mem_filter.mpr ⟨hdom d hd, hqr d hd q hq⟩)
        (hnd.filter _)
        (fun d hd r hr => hqr d hd r (Finset.mem_of_mem_erase hr))
    · exact ih good c prodS h.1 s
        (fun r hr => (List.mem_cons.mp (hsub r hr)).resolve_left (fun e => hq (e ▸ hr)))
        hpos_tail hprodS hdom hnd hqr

private lemma tail_card_le_maxTailCount {b : ℕ} (hb : 0 < b) (hb_lt : b < 1500000000) :
    let s := b.primeFactors ∩ smallPrimesSet
    let t := b.primeFactors \ smallPrimesSet
    t.card ≤ maxTailCount (∏ q ∈ s, q) := by
  intro s t
  have hdisj : Disjoint s t := disjoint_sdiff_self_right.mono_left Finset.inter_subset_right
  have hunion : s ∪ t = b.primeFactors := by
    ext q; simp only [s, t, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    by_cases hq : q ∈ smallPrimesSet <;> simp [hq]
  have hprod_dvd : (∏ q ∈ s, q) * (∏ q ∈ t, q) ∣ b := by
    rw [← Finset.prod_union hdisj, hunion]
    exact Nat.prod_primeFactors_dvd b
  have hprod_le : (∏ q ∈ s, q) * (∏ q ∈ t, q) ≤ 1500000000 :=
    (Nat.le_of_dvd hb hprod_dvd).trans hb_lt.le
  have ht_ge29 : ∀ q ∈ t, 29 ≤ q := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
    have hqns : q ∉ smallPrimesSet := (Finset.mem_sdiff.mp hq).2
    by_contra hlt
    have hcheck : ∀ x : Fin 29, x.val.Prime → x.val ∈ smallPrimesSet := by decide
    exact hqns (hcheck ⟨q, by omega⟩ hqp)
  have hpow29 : 29 ^ t.card ≤ ∏ q ∈ t, q := by
    calc 29 ^ t.card = ∏ _q ∈ t, 29 := by rw [Finset.prod_const]
      _ ≤ ∏ q ∈ t, q := Finset.prod_le_prod (fun _ _ => by omega) ht_ge29
  have hprodS_pos : 1 ≤ ∏ q ∈ s, q := Finset.prod_pos fun q hq =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hq).1).pos
  have ht_le5 : t.card ≤ 5 := by
    by_contra h6
    let M5 : Finset ℕ := {29, 31, 37, 41, 43}
    let u := t ∩ M5
    let v := t \ M5
    have huv_disj : Disjoint u v := disjoint_sdiff_self_right.mono_left Finset.inter_subset_right
    have huv_union : u ∪ v = t := by
      ext q; simp only [u, v, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      by_cases hq : q ∈ M5 <;> simp [hq]
    have hv_ge47 : ∀ q ∈ v, 47 ≤ q := by
      intro q hq
      have hqt : q ∈ t := (Finset.mem_sdiff.mp hq).1
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hqt).1
      have hq29 : 29 ≤ q := ht_ge29 q hqt
      have hqn : q ∉ M5 := (Finset.mem_sdiff.mp hq).2
      by_contra hlt
      have hcheck : ∀ x : Fin 47, 29 ≤ x.val → x.val.Prime → x.val ∈ M5 := by decide
      exact hqn (hcheck ⟨q, by omega⟩ hq29 hqp)
    have hcard_uv : u.card + v.card = t.card := by
      rw [← Finset.card_union_of_disjoint huv_disj, huv_union]
    have hprod_t : (∏ q ∈ u, q) * 47 ^ (6 - u.card) ≤ ∏ q ∈ t, q := by
      rw [← huv_union, Finset.prod_union huv_disj]
      apply Nat.mul_le_mul_left
      calc 47 ^ (6 - u.card) ≤ 47 ^ v.card := Nat.pow_le_pow_right (by decide) (by omega)
        _ = ∏ _q ∈ v, 47 := (Finset.prod_const 47).symm
        _ ≤ ∏ q ∈ v, q := Finset.prod_le_prod (fun _ _ => by omega) hv_ge47
    have hcheck32 : ∀ u' ∈ M5.powerset, 1500000000 < (∏ q ∈ u', q) * 47 ^ (6 - u'.card) := by
      decide +kernel
    have hgt := hcheck32 u (Finset.mem_powerset.mpr Finset.inter_subset_right)
    have hgt2 : 1500000000 < ∏ q ∈ t, q := hgt.trans_le hprod_t
    nlinarith
  have hprod29_le : (∏ q ∈ s, q) * 29 ^ t.card ≤ 1500000000 :=
    (Nat.mul_le_mul_left _ hpow29).trans hprod_le
  unfold maxTailCount
  split_ifs with h5 h4 h3 h2 h1
  · exact ht_le5
  · by_contra h; have : t.card = 5 := by omega
    rw [this] at hprod29_le; exact h5 hprod29_le
  · by_contra h
    have : 4 ≤ t.card := by omega
    have : 29 ^ 4 ≤ 29 ^ t.card := Nat.pow_le_pow_right (by decide) this
    exact h4 ((Nat.mul_le_mul_left _ this).trans hprod29_le)
  · by_contra h
    have : 3 ≤ t.card := by omega
    have : 29 ^ 3 ≤ 29 ^ t.card := Nat.pow_le_pow_right (by decide) this
    exact h3 ((Nat.mul_le_mul_left _ this).trans hprod29_le)
  · by_contra h
    have : 2 ≤ t.card := by omega
    have : 29 ^ 2 ≤ 29 ^ t.card := Nat.pow_le_pow_right (by decide) this
    exact h2 ((Nat.mul_le_mul_left _ this).trans hprod29_le)
  · by_contra h
    have : 1 ≤ t.card := by omega
    have : 29 ^ 1 ≤ 29 ^ t.card := Nat.pow_le_pow_right (by decide) this
    exact h1 ((Nat.mul_le_mul_left _ (by simpa using this)).trans hprod29_le)

private theorem large_primes_any {N b : ℕ} (hN_pos : 0 < N) (hN_hi : N < 1500000000)
    (hb_pos : 0 < b) (hb_le : b ≤ N) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a ≤ N ∧ ∃ p : ℕ, N < 48 * p ∧ p ^ 2 ∣ a * b + 1) :
    S.card ≤ 161792 := by
  classical
  let p (a : ℕ) := if h : a ∈ S then (hS a h).2.choose else 1
  let d (a : ℕ) := (a * b + 1) / (p a) ^ 2
  have hinfo (a : ℕ) (ha : a ∈ S) : N < 48 * p a ∧ (p a) ^ 2 ∣ a * b + 1 := by
    simpa only [p, dif_pos ha] using (hS a ha).2.choose_spec
  have heq (a : ℕ) (ha : a ∈ S) : d a * (p a) ^ 2 = b * a + 1 := by
    rw [Nat.mul_comm b a]
    exact Nat.div_mul_cancel (hinfo a ha).2
  have hd_pos (a : ℕ) (ha : a ∈ S) : 1 ≤ d a := by
    by_contra h0; have hz : d a = 0 := by omega
    have e := heq a ha; rw [hz, zero_mul] at e; omega
  have hd_lt (a : ℕ) (ha : a ∈ S) : d a < 2304 := by
    have haN : a ≤ N := (hS a ha).1
    have hbig : N < 48 * p a := (hinfo a ha).1
    have h1 : b * a + 1 ≤ N * N + 1 := by nlinarith
    have h2 : N ^ 2 < 2304 * (p a) ^ 2 := by nlinarith
    have h3 : d a * (p a) ^ 2 = b * a + 1 := heq a ha
    have hp_pos : 1 ≤ p a := by omega
    by_contra hge
    have : 2304 * (p a) ^ 2 ≤ d a * (p a) ^ 2 := Nat.mul_le_mul_right _ (by omega)
    -- Also b*a + 1 <= N*N + 1, wait: if N^2 + 1 <= 2304*(p a)^2?
    -- Since N < 48*p a, N + 1 <= 48*p a, so N^2 + 1 < (N+1)^2 <= 2304*(p a)^2!
    have h4 : N * N + 1 < (N + 1) * (N + 1) := by nlinarith
    have h5 : (N + 1) * (N + 1) ≤ (48 * p a) * (48 * p a) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  let D : Finset ℕ := S.image d
  have hD_dom : ∀ x ∈ D, x ∈ initDivs48 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (hd_lt a ha), decide_eq_true (hd_pos a ha)⟩
  let s := b.primeFactors ∩ smallPrimesSet
  have hD_qr : ∀ x ∈ D, ∀ q ∈ s, qr q x = true := by
    intro x hx q hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have hq_mem : q ∈ smallPrimesSet := (Finset.mem_inter.mp hq).2
    have hqb : q ∣ b := Nat.dvd_of_mem_primeFactors (Finset.mem_inter.mp hq).1
    exact qr_sound_small hq_mem hqb (heq a ha)
  -- Partition S by d a, then by unitary root key g ∈ U
  let U := b.divisors.filter (fun g => (Nat.gcd g (b / g)) ∣ 2)
  have hS_split : S.card = ∑ x ∈ D, (S.filter (fun a => d a = x)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext a; simp only [Finset.mem_biUnion, Finset.mem_filter, D, Finset.mem_image]
      exact ⟨fun ha => ⟨d a, ⟨a, ha, rfl⟩, ha, rfl⟩, fun ⟨_, _, ha, _⟩ => ha⟩
    · intro x₁ _ x₂ _ hne
      exact Finset.disjoint_filter.mpr fun a _ h1 h2 => hne (h1.symm.trans h2)
  have hfiber_d : ∀ x ∈ D, (S.filter (fun a => d a = x)).card ≤ U.card * (1 + 47 / x) := by
    intro x hx
    let Sx := S.filter (fun a => d a = x)
    obtain ⟨r0, hr0_S, hr0_d⟩ := Finset.mem_image.mp hx
    have hr0_eq : (x : ℤ) * (p r0 : ℤ) ^ 2 = (b : ℤ) * (r0 : ℤ) + 1 := by
      exact_mod_cast (hr0_d ▸ heq r0 hr0_S)
    let key (a : ℕ) : ℕ := Int.gcd (b : ℤ) ((p a : ℤ) - (p r0 : ℤ))
    have hkey_mem : ∀ a ∈ Sx, key a ∈ U := by
      intro a ha
      have haS : a ∈ S := (Finset.mem_filter.mp ha).1
      have had : d a = x := (Finset.mem_filter.mp ha).2
      have ha_eq : (x : ℤ) * (p a : ℤ) ^ 2 = (b : ℤ) * (a : ℤ) + 1 := by
        exact_mod_cast (had ▸ heq a haS)
      have hgb : key a ∣ b := by
        dsimp only [key]
        exact_mod_cast Int.gcd_dvd_left (b : ℤ) ((p a : ℤ) - (p r0 : ℤ))
      exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hgb, hb_pos.ne'⟩,
        root_key_valid hb_pos hr0_eq ha_eq⟩
    have hSx_split : Sx.card = ∑ g ∈ U, (Sx.filter (fun a => key a = g)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext a; simp only [Finset.mem_biUnion, Finset.mem_filter]
        exact ⟨fun ha => ⟨key a, hkey_mem a ha, ha, rfl⟩, fun ⟨_, _, ha, _⟩ => ha⟩
      · intro g₁ _ g₂ _ hne
        exact Finset.disjoint_filter.mpr fun a _ h1 h2 => hne (h1.symm.trans h2)
    rw [hSx_split]
    calc ∑ g ∈ U, (Sx.filter (fun a => key a = g)).card
        ≤ ∑ _g ∈ U, (1 + 47 / x) := by
          refine Finset.sum_le_sum fun g _ => ?_
          let Sxg := Sx.filter (fun a => key a = g)
          have hpinj : Set.InjOn p (Sxg : Set ℕ) := by
            intro a₁ h₁ a₂ h₂ hpeq
            have ha₁S := (Finset.mem_filter.mp (Finset.mem_filter.mp h₁).1).1
            have ha₂S := (Finset.mem_filter.mp (Finset.mem_filter.mp h₂).1).1
            have hd₁ := (Finset.mem_filter.mp (Finset.mem_filter.mp h₁).1).2
            have hd₂ := (Finset.mem_filter.mp (Finset.mem_filter.mp h₂).1).2
            have e1 := hd₁ ▸ heq a₁ ha₁S
            have e2 := hd₂ ▸ heq a₂ ha₂S
            rw [hpeq] at e1
            have : b * a₁ = b * a₂ := by omega
            exact Nat.eq_of_mul_eq_mul_left hb_pos this
          have hstep : ∀ a₁ ∈ Sxg, ∀ a₂ ∈ Sxg, p a₁ < p a₂ → b ≤ 2 * (p a₂ - p a₁) := by
            intro a₁ h₁ a₂ h₂ hlt
            have ha₁S := (Finset.mem_filter.mp (Finset.mem_filter.mp h₁).1).1
            have ha₂S := (Finset.mem_filter.mp (Finset.mem_filter.mp h₂).1).1
            have hd₁ := (Finset.mem_filter.mp (Finset.mem_filter.mp h₁).1).2
            have hd₂ := (Finset.mem_filter.mp (Finset.mem_filter.mp h₂).1).2
            have hk₁ : key a₁ = g := (Finset.mem_filter.mp h₁).2
            have hk₂ : key a₂ = g := (Finset.mem_filter.mp h₂).2
            have e1 : (x : ℤ) * (p a₁ : ℤ) ^ 2 = (b : ℤ) * (a₁ : ℤ) + 1 := by exact_mod_cast (hd₁ ▸ heq a₁ ha₁S)
            have e2 : (x : ℤ) * (p a₂ : ℤ) ^ 2 = (b : ℤ) * (a₂ : ℤ) + 1 := by exact_mod_cast (hd₂ ▸ heq a₂ ha₂S)
            have hdvd : (b : ℤ) ∣ 2 * ((p a₂ : ℤ) - (p a₁ : ℤ)) :=
              roots_in_class hr0_eq e1 e2 (hk₁.trans hk₂.symm)
            have hdvd_nat : b ∣ 2 * (p a₂ - p a₁) := by
              have : (2 * (p a₂ - p a₁) : ℕ) = ((2 * ((p a₂ : ℤ) - (p a₁ : ℤ))).toNat) := by omega
              exact_mod_cast (show (b : ℤ) ∣ ((2 * (p a₂ - p a₁) : ℕ) : ℤ) by
                push_cast [Nat.cast_sub hlt.le]; exact hdvd)
            exact Nat.le_of_dvd (by omega) hdvd_nat
          exact card_chain_le_of_step hb_pos (hr0_d ▸ hd_pos r0 hr0_S) hN_pos p hpinj
            (fun a ha => (hS a (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1).1)
            (fun a ha => (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2 ▸
              heq a (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1)
            (fun a ha => (hinfo a (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1).1)
            hstep
      _ = U.card * (1 + 47 / x) := by rw [Finset.sum_const, smul_eq_mul]
  have hcard_le : S.card ≤ U.card * ∑ x ∈ D, (1 + 47 / x) := by
    rw [hS_split, Finset.mul_sum]
    exact Finset.sum_le_sum hfiber_d
  have hU_le : U.card ≤ 2 * 2 ^ b.primeFactors.card := count_unitary_keys b hb_pos
  let t := b.primeFactors \ smallPrimesSet
  have hst_card : s.card + t.card = b.primeFactors.card := by
    rw [Nat.add_comm]; exact Finset.card_sdiff_add_card_inter _ _
  have ht_le : t.card ≤ maxTailCount (∏ q ∈ s, q) :=
    tail_card_le_maxTailCount hb_pos (hb_le.trans_lt hN_hi)
  have hprod_s_le : ∏ q ∈ s, q ≤ 1500000000 := by
    have hdvd : (∏ q ∈ s, q) ∣ b :=
      (Finset.prod_dvd_prod_of_subset _ _ _ Finset.inter_subset_left).trans (Nat.prod_primeFactors_dvd b)
    exact (Nat.le_of_dvd hb_pos hdvd).trans (hb_le.trans hN_hi.le)
  have hwalk := walkLarge_sound smallPrimesList initDivs48 0 1 walkLarge_ok s D
    (fun q hq => by
      have := (Finset.mem_inter.mp hq).2
      simpa [smallPrimesList, smallPrimesSet] using this)
    (by decide)
    (by simpa using hprod_s_le)
    hD_dom
    ((List.nodup_range).filter _)
    hD_qr
  simp only [Nat.zero_add, one_mul] at hwalk
  have hpow_le : 2 ^ b.primeFactors.card ≤ 2 ^ (s.card + maxTailCount (∏ q ∈ s, q)) := by
    rw [← hst_card]
    exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left ht_le s.card)
  calc S.card
      ≤ U.card * ∑ x ∈ D, (1 + 47 / x) := hcard_le
    _ ≤ (2 * 2 ^ b.primeFactors.card) * ∑ x ∈ D, (1 + 47 / x) := Nat.mul_le_mul_right _ hU_le
    _ ≤ (2 * 2 ^ (s.card + maxTailCount (∏ q ∈ s, q))) * ∑ x ∈ D, (1 + 47 / x) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hpow_le)
    _ ≤ 161792 := hwalk

/-! ### Section 3: Prime Counting via `Chebyshev.theta` and Diagonal Gap -/

private theorem count_by_theta_refined (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2) :
    e * N.primeCounting ≤ e * M.primeCounting + 2 * N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ M.primesLE := fun q hq =>
    Nat.mem_primesLE.mpr ⟨(Finset.mem_filter.mp hq).2, (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2⟩
  have hsmall := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at hsmall
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := Finset.sum_le_sum fun q hq =>
          Real.log_le_log (by exact_mod_cast Mpos)
            (by exact_mod_cast Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := Finset.sum_le_sum_of_subset_of_nonneg filterSub
          fun q hq _ => Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower; rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M.primeCounting := by exact_mod_cast hsmall
  exact_mod_cast (show e * (N.primeCounting : ℝ) ≤ e * (M.primeCounting : ℝ) + 2 * (N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0 : ℝ) ≤ (e : ℝ) by positivity)])

private theorem log_nat_two_pow (n : ℕ) : Real.log ((2 ^ n : ℕ) : ℝ) = n * Real.log 2 := by
  rw [Nat.cast_pow, Real.log_pow]; norm_num

private theorem prime_count_div {N K : ℕ} (hK : 0 < K) (Q : Finset ℕ) (pr : ∀ p ∈ Q, p.Prime)
    (cut : ∀ p ∈ Q, K * p ≤ N) :
    17 * K * Q.card ≤ 2 * N + 17 * K * 25880 := by
  let X := N / K
  have sub : Q ⊆ X.primesLE := fun p hp =>
    Nat.mem_primesLE.mpr ⟨(Nat.le_div_iff_mul_le hK).mpr (by rw [Nat.mul_comm]; exact cut p hp), pr p hp⟩
  have bound := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at bound
  have top := count_by_theta_refined X (2 ^ 17) 17 (by decide) (log_nat_two_pow 17)
  have med := count_by_theta_refined (2 ^ 17) (2 ^ 11) 11 (by decide) (log_nat_two_pow 11)
  have sub' : (2 ^ 11).primesLE ⊆ Finset.Icc 1 (2 ^ 11) := fun i hi =>
    Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hi).2.pos, (Nat.mem_primesLE.mp hi).1⟩
  have mid := Finset.card_le_card sub'
  rw [Nat.primesLE_card_eq_primeCounting] at mid
  norm_num only [Nat.card_Icc] at mid
  simp only [show (2 ^ 17 : ℕ) = 131072 by decide, show (2 ^ 11 : ℕ) = 2048 by decide] at top med mid
  have h1 : 17 * Q.card ≤ 17 * 25880 + 2 * X := by omega
  have hX : K * X ≤ N := Nat.mul_div_le N K
  have h2 := Nat.mul_le_mul_left K h1
  nlinarith

private theorem diagonal_gap {d n m p q : ℕ} (pp : 2 ≤ p) (pq : p < q) (narrow : q ≤ 2 * p)
    (hn : n ^ 2 + 1 = d * p ^ 2) (hm : m ^ 2 + 1 = d * q ^ 2) : False := by
  have dp : 0 < d := by cases d with | zero => simp at hn | succ d => omega
  have coord {k t : ℕ} (hk : 2 ≤ k) (eq : t ^ 2 + 1 = d * k ^ 2) : k ≤ t := by
    have pd : k ^ 2 ≤ d * k ^ 2 := by simpa using Nat.mul_le_mul_right (k ^ 2) dp
    have sq2 : 4 ≤ k ^ 2 := Nat.pow_le_pow_left hk 2
    have pos : 0 < t := by cases t with | zero => simp at eq; omega | succ t => omega
    by_contra h
    have sq := Nat.pow_le_pow_left (show t + 1 ≤ k by omega) 2
    nlinarith only [sq, pd, eq, pos]
  have pm := coord pp hn
  have prod : (m * p) ^ 2 + p ^ 2 = (n * q) ^ 2 + q ^ 2 := by
    have a := congrArg (· * p ^ 2) hm
    have b := congrArg (· * q ^ 2) hn
    nlinarith only [a, b]
  have sq_lt := Nat.pow_lt_pow_left pq (by decide : 2 ≠ 0)
  have det : n * q < m * p := by
    by_contra h; have leq := Nat.pow_le_pow_left (show m * p ≤ n * q by omega) 2; omega
  have detsq := Nat.pow_le_pow_left (show n * q + 1 ≤ m * p by omega) 2
  have hmul := Nat.mul_le_mul_right q pm
  have qt := Nat.mul_le_mul_right q narrow
  nlinarith only [detsq, prod, qt, hmul]

private theorem large_diagonal_150 {N : ℕ} (hN : 160000000 ≤ N) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a ≤ N ∧ ∃ p : ℕ, p.Prime ∧ N < 150 * p ∧ p ^ 2 ∣ a ^ 2 + 1) :
    S.card ≤ 60000 := by
  classical
  let p (a : ℕ) := if h : a ∈ S then (hS a h).2.choose else 1
  let d (a : ℕ) := (a ^ 2 + 1) / (p a) ^ 2
  have hinfo (a : ℕ) (ha : a ∈ S) : (p a).Prime ∧ N < 150 * p a ∧ (p a) ^ 2 ∣ a ^ 2 + 1 := by
    simpa only [p, dif_pos ha] using (hS a ha).2.choose_spec
  have heq (a : ℕ) (ha : a ∈ S) : a ^ 2 + 1 = d a * (p a) ^ 2 :=
    (Nat.div_mul_cancel (hinfo a ha).2.2).symm
  have hp_le (a : ℕ) (ha : a ∈ S) : p a ≤ N := by
    have haN := (hS a ha).1
    have hd1 : 1 ≤ d a := by
      by_contra h0; have hz : d a = 0 := by omega
      have e := heq a ha; rw [hz, zero_mul] at e; omega
    have h1 : (p a) ^ 2 ≤ a ^ 2 + 1 := by nlinarith [heq a ha]
    have h2 : a ^ 2 + 1 < (N + 1) ^ 2 := by nlinarith
    by_contra hgt; have : (N + 1) ^ 2 ≤ (p a) ^ 2 := Nat.pow_le_pow_left (by omega) 2; omega
  have hd_lt (a : ℕ) (ha : a ∈ S) : d a < 22500 := by
    have haN := (hS a ha).1
    have hbig := (hinfo a ha).2.1
    have h1 : a ^ 2 + 1 < (N + 1) ^ 2 := by nlinarith
    have h2 : (N + 1) ^ 2 ≤ (150 * p a) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    by_contra hge
    have : 22500 * (p a) ^ 2 ≤ d a * (p a) ^ 2 := Nat.mul_le_mul_right _ (by omega)
    nlinarith [heq a ha]
  have hd_mod (a : ℕ) (ha : a ∈ S) : (d a % 4 = 1 ∨ d a % 4 = 2) ∧ d a % 3 ≠ 0 := by
    have e := heq a ha
    have hp_ge3 : 3 ≤ p a := by
      have hp2 := (hinfo a ha).1.two_le
      have hbig := (hinfo a ha).2.1
      omega
    have hp_odd : (p a) % 2 = 1 := by
      rcases (hinfo a ha).1.eq_two_or_odd with h2 | ho
      · omega
      · exact ho
    have hp2_mod4 : (p a) ^ 2 % 4 = 1 := by
      have : p a = 2 * (p a / 2) + 1 := by omega
      rw [this]; ring_nf; omega
    have ha2_mod4 : (a ^ 2 + 1) % 4 = 1 ∨ (a ^ 2 + 1) % 4 = 2 := by
      have : a = 2 * (a / 2) + a % 2 := by omega
      have hmod2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      rcases hmod2 with h0 | h1
      · left; rw [this, h0]; ring_nf; omega
      · right; rw [this, h1]; ring_nf; omega
    have hd4 : d a % 4 = 1 ∨ d a % 4 = 2 := by
      have h := congrArg (· % 4) e
      rw [Nat.mul_mod, hp2_mod4, mul_one, Nat.mod_mod] at h
      omega
    have hd3 : d a % 3 ≠ 0 := by
      intro h3
      have h3dvd : 3 ∣ a ^ 2 + 1 := e ▸ dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero h3) _
      have hmod3 : ((a % 3) ^ 2 + 1) % 3 = 0 := by
        have h0 : (a ^ 2 + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h3dvd
        rw [Nat.add_mod, Nat.pow_mod, ← Nat.add_mod] at h0; exact h0
      have hcheck : ∀ r : Fin 3, (r.val ^ 2 + 1) % 3 ≠ 0 := by decide
      exact hcheck ⟨a % 3, Nat.mod_lt _ (by decide)⟩ hmod3
    exact ⟨hd4, hd3⟩
  -- Dyadic band j ∈ {0..7}: N < 2^(j+1) * p a ∧ 2^j * p a ≤ N
  let band (a : ℕ) : ℕ := Nat.log 2 (N / p a)
  have hband_lt (a : ℕ) (ha : a ∈ S) : band a < 8 := by
    have hdiv_lt : N / p a < 150 := (Nat.div_lt_iff_lt_mul (hinfo a ha).1.pos).mpr (hinfo a ha).2.1
    have hlt256 : N / p a < 2 ^ 8 := lt_trans hdiv_lt (by decide)
    exact Nat.log_lt_of_lt_pow (by
      have := hp_le a ha
      exact (Nat.div_pos this (hinfo a ha).1.pos).ne') hlt256
  let key (a : ℕ) : (ℕ × ℕ) × ℕ := ((d a / 12, d a % 12), band a)
  have hinj : Set.InjOn key (S : Set ℕ) := by
    intro a₁ h₁ a₂ h₂ hk
    have ⟨hd_pair, hb_eq⟩ := Prod.mk.inj hk
    have ⟨hd_div, hd_rem⟩ := Prod.mk.inj hd_pair
    have hd_eq : d a₁ = d a₂ := by omega
    by_contra hne
    have hp_ne : p a₁ ≠ p a₂ := by
      intro hp_eq
      have e1 := heq a₁ h₁; have e2 := heq a₂ h₂
      rw [hd_eq, hp_eq] at e1
      have : a₁ ^ 2 = a₂ ^ 2 := by omega
      exact hne (by nlinarith)
    have hband_bounds : ∀ a ∈ S, 2 ^ (band a) * p a ≤ N ∧ N < 2 ^ (band a + 1) * p a := by
      intro a ha
      have hpos : 0 < N / p a := Nat.div_pos (hp_le a ha) (hinfo a ha).1.pos
      have hlo : 2 ^ (band a) ≤ N / p a := Nat.pow_log_le_self 2 hpos.ne'
      have hhi : N / p a < 2 ^ (band a + 1) := Nat.lt_pow_succ_log_self (by decide) _
      constructor
      · exact (Nat.le_div_iff_mul_le (hinfo a ha).1.pos).mp hlo
      · exact (Nat.div_lt_iff_lt_mul (hinfo a ha).1.pos).mp hhi
    have ⟨hlo1, hhi1⟩ := hband_bounds a₁ h₁
    have ⟨hlo2, hhi2⟩ := hband_bounds a₂ h₂
    rw [hb_eq] at hlo1 hhi1
    rcases lt_or_gt_of_ne hp_ne with hlt | hgt
    · have h2p : p a₂ ≤ 2 * p a₁ := by
        have h1 : 2 ^ (band a₂) * p a₂ ≤ N := hlo2
        have h2 : N < 2 ^ (band a₂) * (2 * p a₁) := by rw [pow_succ'] at hhi1; linarith
        exact (Nat.lt_of_mul_lt_mul_left (h1.trans_lt h2)).le
      exact diagonal_gap (hinfo a₁ h₁).1.two_le hlt h2p (heq a₁ h₁) (hd_eq ▸ heq a₂ h₂)
    · have h2p : p a₁ ≤ 2 * p a₂ := by
        have h1 : 2 ^ (band a₂) * p a₁ ≤ N := hlo1
        have h2 : N < 2 ^ (band a₂) * (2 * p a₂) := by rw [pow_succ'] at hhi2; linarith
        exact (Nat.lt_of_mul_lt_mul_left (h1.trans_lt h2)).le
      exact diagonal_gap (hinfo a₂ h₂).1.two_le hgt h2p (hd_eq ▸ heq a₂ h₂) (heq a₁ h₁)
  let r4 (n : ℕ) : Fin 4 :=
    if n % 12 = 1 then 0 else if n % 12 = 2 then 1 else if n % 12 = 5 then 2 else 3
  let fkey (a : ℕ) : (Fin 1875 × Fin 4) × Fin 8 :=
    ((⟨(d a / 12) % 1875, Nat.mod_lt _ (by decide)⟩, r4 (d a)), ⟨band a % 8, Nat.mod_lt _ (by decide)⟩)
  have hfinj : Set.InjOn fkey (S : Set ℕ) := by
    intro a₁ h₁ a₂ h₂ hk
    have ⟨h1, h2⟩ := Prod.mk.inj hk
    have ⟨hdiv, hrem⟩ := Prod.mk.inj h1
    have hdiv_v : d a₁ / 12 = d a₂ / 12 := by
      have := congrArg Fin.val hdiv
      dsimp only at this
      rw [Nat.mod_eq_of_lt (by have := hd_lt a₁ h₁; omega), Nat.mod_eq_of_lt (by have := hd_lt a₂ h₂; omega)] at this
      exact this
    have hb_v : band a₁ = band a₂ := by
      have := congrArg Fin.val h2
      dsimp only at this
      rw [Nat.mod_eq_of_lt (hband_lt a₁ h₁), Nat.mod_eq_of_lt (hband_lt a₂ h₂)] at this
      exact this
    have hrem_v : d a₁ % 12 = d a₂ % 12 := by
      have ⟨h41, h31⟩ := hd_mod a₁ h₁
      have ⟨h42, h32⟩ := hd_mod a₂ h₂
      have hm1 : d a₁ % 12 = 1 ∨ d a₁ % 12 = 2 ∨ d a₁ % 12 = 5 ∨ d a₁ % 12 = 10 := by omega
      have hm2 : d a₂ % 12 = 1 ∨ d a₂ % 12 = 2 ∨ d a₂ % 12 = 5 ∨ d a₂ % 12 = 10 := by omega
      rcases hm1 with u | u | u | u <;> rcases hm2 with v | v | v | v <;> simp [r4, u, v] at hrem ⊢
    exact hinj h₁ h₂ (by simp only [key, hdiv_v, hrem_v, hb_v])
  have hle : S.card ≤ Fintype.card ((Fin 1875 × Fin 4) × Fin 8) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_le_of_injective (fun x : S => fkey x.1) fun x y h =>
      Subtype.ext (hfinj x.2 y.2 h)
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at hle
  exact hle

/-! ### Section 4: Residue-Class Sieve & Certified Finite Prime Sums -/

private lemma card_Icc_mod_eq_le (N m r : ℕ) (hm : 0 < m) :
    ((Finset.Icc 1 N).filter (fun a => a % m = r % m)).card ≤ N / m + 1 := by
  have hsub : (Finset.Icc 1 N).filter (fun a => a % m = r % m) ⊆
      (Finset.range (N / m + 1)).image (fun q => q * m + r % m) := by
    intro a ha
    have ⟨haI, ham⟩ := Finset.mem_filter.mp ha
    have haN := (Finset.mem_Icc.mp haI).2
    refine Finset.mem_image.mpr ⟨a / m, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right haN)), ?_⟩
    rw [← ham, Nat.mul_comm (a / m) m, Nat.add_comm, Nat.mod_add_div]
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

private lemma card_Icc_mod_and_dvd_le {N m p b r : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hcop : Nat.Coprime m (p ^ 2)) (hpb : ¬ p ∣ b) :
    ((Finset.Icc 1 N).filter (fun a => a % m = r % m ∧ p ^ 2 ∣ a * b + 1)).card ≤
      N / (m * p ^ 2) + 1 := by
  have hcop_bp : Nat.Coprime b (p ^ 2) := hp.coprime_pow_of_not_dvd (m := 2) hpb
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  let rZ : ZMod (p ^ 2) := -((b : ZMod (p ^ 2))⁻¹)
  let t : ℕ := rZ.val
  have htZ : (t : ZMod (p ^ 2)) = rZ := ZMod.natCast_zmod_val rZ
  let c : ℕ := (Nat.chineseRemainder hcop r t).val
  have hsub : (Finset.Icc 1 N).filter (fun a => a % m = r % m ∧ p ^ 2 ∣ a * b + 1) ⊆
      (Finset.Icc 1 N).filter (fun a => a % (m * p ^ 2) = c % (m * p ^ 2)) := by
    intro a ha
    obtain ⟨haI, ham, hdvd⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨haI, ?_⟩
    have ha1 : a ≡ r [MOD m] := ham
    have ha2 : a ≡ t [MOD p ^ 2] := by
      have hz : ((a * b + 1 : ℕ) : ZMod (p ^ 2)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      have hz' : (a : ZMod (p ^ 2)) * (b : ZMod (p ^ 2)) = -1 := by
        have : (a : ZMod (p ^ 2)) * (b : ZMod (p ^ 2)) + 1 = 0 := by simpa using hz
        exact eq_neg_of_add_eq_zero_left this
      have hbUnit : IsUnit (b : ZMod (p ^ 2)) := (ZMod.isUnit_iff_coprime b (p ^ 2)).mpr hcop_bp
      have haZ : (a : ZMod (p ^ 2)) = rZ := by
        have h1 := congrArg (· * (b : ZMod (p ^ 2))⁻¹) hz'
        rw [mul_assoc, ZMod.mul_inv_of_unit _ hbUnit, mul_one] at h1
        simpa [rZ] using h1
      rw [← htZ] at haZ
      exact (ZMod.natCast_eq_natCast_iff a t (p ^ 2)).mp haZ
    exact Nat.chineseRemainder_modEq_unique hcop ha1 ha2
  exact (Finset.card_le_card hsub).trans (card_Icc_mod_eq_le N (m * p ^ 2) c (Nat.mul_pos hm (pow_pos hp.pos 2)))

private lemma card_Icc_dvd_ab_le {N p b : ℕ} (hp : p.Prime) (hpb : ¬ p ∣ b) :
    ((Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a * b + 1)).card ≤ N / p ^ 2 + 1 := by
  have h := card_Icc_mod_and_dvd_le (N := N) (m := 1) (p := p) (b := b) (r := 0)
    (by decide) hp (Nat.coprime_one_left _) hpb
  simpa [Nat.mod_one] using h

private lemma card_Icc_dvd_ab_le_one {N p b : ℕ} (hp : p.Prime) (hpb : ¬ p ∣ b) (hbig : N < p ^ 2) :
    ((Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a * b + 1)).card ≤ 1 := by
  have h := card_Icc_dvd_ab_le (N := N) hp hpb
  rw [Nat.div_eq_of_lt hbig] at h
  exact h

/-- For a prime `p ≡ 1 (mod 4)`, `a^2 + 1 ≡ 0 (mod p^2)` has at most 2 solutions modulo `p^2`
(namely `r` and `p^2 - r`). -/
private lemma sq_add_one_roots_mod_p2 {p : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2) :
    ∃ r₁ r₂ : ℕ, r₁ < p ^ 2 ∧ r₂ < p ^ 2 ∧ r₁ + r₂ = p ^ 2 ∧
      ∀ a : ℕ, p ^ 2 ∣ a ^ 2 + 1 → a % p ^ 2 = r₁ ∨ a % p ^ 2 = r₂ := by
  by_cases hex : ∃ a : ℕ, p ^ 2 ∣ a ^ 2 + 1
  · obtain ⟨a0, ha0⟩ := hex
    let r₁ := a0 % p ^ 2
    have hr₁_lt : r₁ < p ^ 2 := Nat.mod_lt _ (pow_pos hp.pos 2)
    have hr₁_pos : 0 < r₁ := Nat.pos_of_ne_zero fun hz => by
      have hp2a : p ^ 2 ∣ a0 := Nat.dvd_of_mod_eq_zero hz
      have hpa0 : p ∣ a0 := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hp2a
      have hpa01 : p ∣ a0 ^ 2 + 1 := (dvd_pow_self p (by decide : 2 ≠ 0)).trans ha0
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_pow hpa0 (by decide : 2 ≠ 0))).mp hpa01)
    let r₂ := p ^ 2 - r₁
    refine ⟨r₁, r₂, hr₁_lt, by dsimp [r₂]; omega, by dsimp [r₂]; omega, fun a ha => ?_⟩
    have hdiff : (p ^ 2 : ℤ) ∣ (a : ℤ) ^ 2 - (a0 : ℤ) ^ 2 := by
      have h1 : (p ^ 2 : ℤ) ∣ (a : ℤ) ^ 2 + 1 := by exact_mod_cast ha
      have h2 : (p ^ 2 : ℤ) ∣ (a0 : ℤ) ^ 2 + 1 := by exact_mod_cast ha0
      have hsub := dvd_sub h1 h2
      rwa [show ((a : ℤ) ^ 2 + 1) - ((a0 : ℤ) ^ 2 + 1) = (a : ℤ) ^ 2 - (a0 : ℤ) ^ 2 by ring] at hsub
    have hfac : (p ^ 2 : ℤ) ∣ ((a : ℤ) - (a0 : ℤ)) * ((a : ℤ) + (a0 : ℤ)) := by
      rwa [show (a : ℤ) ^ 2 - (a0 : ℤ) ^ 2 = ((a : ℤ) - (a0 : ℤ)) * ((a : ℤ) + (a0 : ℤ)) by ring] at hdiff
    have hnot_both : ¬ ((p : ℤ) ∣ (a : ℤ) - (a0 : ℤ) ∧ (p : ℤ) ∣ (a : ℤ) + (a0 : ℤ)) := by
      rintro ⟨h1, h2⟩
      have hsum : (p : ℤ) ∣ 2 * (a0 : ℤ) := by
        have hsub := dvd_sub h2 h1
        rwa [show ((a : ℤ) + (a0 : ℤ)) - ((a : ℤ) - (a0 : ℤ)) = 2 * (a0 : ℤ) by ring] at hsub
      have hpa0 : (p : ℤ) ∣ (a0 : ℤ) := by
        have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
        rcases hp_int.dvd_or_dvd hsum with h2d | ha0d
        · exfalso; have : p ∣ 2 := by exact_mod_cast h2d
          have := Nat.le_of_dvd (by decide) this; have := hp.two_le; omega
        · exact ha0d
      have hpa0_nat : p ∣ a0 := by exact_mod_cast hpa0
      have : p ∣ a0 ^ 2 + 1 := (dvd_pow_self p (by decide : 2 ≠ 0)).trans ha0
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_pow hpa0_nat (by decide : 2 ≠ 0))).mp this)
    have hcases : (p ^ 2 : ℤ) ∣ (a : ℤ) - (a0 : ℤ) ∨ (p ^ 2 : ℤ) ∣ (a : ℤ) + (a0 : ℤ) := by
      have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hpd : (p : ℤ) ∣ ((a : ℤ) - (a0 : ℤ)) * ((a : ℤ) + (a0 : ℤ)) :=
        (dvd_pow_self (p : ℤ) (by decide : 2 ≠ 0)).trans hfac
      rcases hp_int.dvd_or_dvd hpd with h1 | h2
      · left
        have hcop : IsCoprime ((p : ℤ) ^ 2) ((a : ℤ) + (a0 : ℤ)) := by
          apply IsCoprime.pow_left
          exact (Prime.coprime_iff_not_dvd hp_int).mpr fun h => hnot_both ⟨h1, h⟩
        exact hcop.dvd_of_dvd_mul_right hfac
      · right
        have hcop : IsCoprime ((p : ℤ) ^ 2) ((a : ℤ) - (a0 : ℤ)) := by
          apply IsCoprime.pow_left
          exact (Prime.coprime_iff_not_dvd hp_int).mpr fun h => hnot_both ⟨h, h2⟩
        exact hcop.dvd_of_dvd_mul_left hfac
    rcases hcases with h1 | h2
    · left
      have hmod : (a : ℤ) % (p ^ 2 : ℤ) = (a0 : ℤ) % (p ^ 2 : ℤ) :=
        Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h1)
      exact_mod_cast hmod
    · right
      have hmod : ((a : ℤ) + (a0 : ℤ)) % (p ^ 2 : ℤ) = 0 := Int.emod_eq_zero_of_dvd h2
      have hnat : (a + a0) % p ^ 2 = 0 := by exact_mod_cast hmod
      have h3 : (a % p ^ 2 + r₁) % p ^ 2 = 0 := by
        change (a % p ^ 2 + a0 % p ^ 2) % p ^ 2 = 0
        rw [← Nat.add_mod]; exact hnat
      have hlt_a : a % p ^ 2 < p ^ 2 := Nat.mod_lt _ (pow_pos hp.pos 2)
      dsimp only [r₁, r₂] at hr₁_lt hr₁_pos h3 ⊢
      by_cases hsum : a % p ^ 2 + a0 % p ^ 2 < p ^ 2
      · rw [Nat.mod_eq_of_lt hsum] at h3
        exact absurd (Nat.add_eq_zero_iff.mp h3).2 hr₁_pos.ne'
      · have hsub : a % p ^ 2 + a0 % p ^ 2 - p ^ 2 < p ^ 2 := by omega
        have h3' : (a % p ^ 2 + a0 % p ^ 2 - p ^ 2) % p ^ 2 = 0 := by
          rw [← Nat.add_mod_right _ (p ^ 2), Nat.sub_add_cancel (by omega)]
          exact h3
        rw [Nat.mod_eq_of_lt hsub] at h3'
        omega
  · have hp2 : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
    refine ⟨1, p ^ 2 - 1, by omega, by omega, by omega, fun a ha => (hex ⟨a, ha⟩).elim⟩

private lemma card_Icc_sq_add_one_le {N p : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2) :
    ((Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a ^ 2 + 1)).card ≤ 2 * (N / p ^ 2 + 1) := by
  obtain ⟨r₁, r₂, hr₁, hr₂, _, hroots⟩ := sq_add_one_roots_mod_p2 hp hp_odd
  have hsub : (Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a ^ 2 + 1) ⊆
      (Finset.Icc 1 N).filter (fun a => a % p ^ 2 = r₁ % p ^ 2) ∪
      (Finset.Icc 1 N).filter (fun a => a % p ^ 2 = r₂ % p ^ 2) := by
    intro a ha
    obtain ⟨haI, hdvd⟩ := Finset.mem_filter.mp ha
    rcases hroots a hdvd with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haI, by rw [Nat.mod_eq_of_lt hr₁]; exact h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haI, by rw [Nat.mod_eq_of_lt hr₂]; exact h2⟩)
  calc ((Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a ^ 2 + 1)).card
      ≤ _ := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    _ ≤ (N / p ^ 2 + 1) + (N / p ^ 2 + 1) :=
        Nat.add_le_add (card_Icc_mod_eq_le N (p ^ 2) r₁ (pow_pos hp.pos 2))
          (card_Icc_mod_eq_le N (p ^ 2) r₂ (pow_pos hp.pos 2))
    _ = 2 * (N / p ^ 2 + 1) := by ring

private lemma card_Icc_sq_add_one_le_one {N p : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2) (hbig : 2 * N < p ^ 2) :
    ((Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a ^ 2 + 1)).card ≤ 1 := by
  obtain ⟨r₁, r₂, hr₁, hr₂, hsum, hroots⟩ := sq_add_one_roots_mod_p2 hp hp_odd
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨haI, ha_dvd⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbI, hb_dvd⟩ := Finset.mem_filter.mp hb
  have haN := (Finset.mem_Icc.mp haI).2
  have hbN := (Finset.mem_Icc.mp hbI).2
  have ha_mod : a % p ^ 2 = a := Nat.mod_eq_of_lt (by omega)
  have hb_mod : b % p ^ 2 = b := Nat.mod_eq_of_lt (by omega)
  rcases hroots a ha_dvd with h1 | h1 <;> rcases hroots b hb_dvd with h2 | h2 <;> omega

private lemma card_Icc_sq_add_one_isStar_le {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.Icc 1 N).filter (fun a => (a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ p ^ 2 ∣ a ^ 2 + 1)).card ≤
      46 * (N / (25 * p ^ 2) + 1) := by
  obtain ⟨r₁, r₂, hr₁, hr₂, _, hroots⟩ := sq_add_one_roots_mod_p2 hp hp2
  have hcop : Nat.Coprime 25 (p ^ 2) := (Nat.prime_five.coprime_iff_not_dvd.mpr fun h =>
    hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp h).symm).pow 2 2
  let R25 := (Finset.range 25).filter (fun u => u ≠ 7 ∧ u ≠ 18)
  have hR25 : R25.card = 23 := by decide +kernel
  have hsub : (Finset.Icc 1 N).filter (fun a => (a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ p ^ 2 ∣ a ^ 2 + 1) ⊆
      (R25 ×ˢ ({r₁, r₂} : Finset ℕ)).biUnion fun ur =>
        (Finset.Icc 1 N).filter (fun a => a % (25 * p ^ 2) = (Nat.chineseRemainder hcop ur.1 ur.2).val % (25 * p ^ 2)) := by
    intro a ha
    obtain ⟨haI, ⟨h7, h18⟩, hdvd⟩ := Finset.mem_filter.mp ha
    rw [Finset.mem_biUnion]
    have ha25 : a % 25 ∈ R25 := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by decide)), h7, h18⟩
    rcases hroots a hdvd with h1 | h2
    · refine ⟨(a % 25, r₁), Finset.mem_product.mpr ⟨ha25, by simp⟩, Finset.mem_filter.mpr ⟨haI, ?_⟩⟩
      exact Nat.chineseRemainder_modEq_unique hcop (by change a % 25 = (a % 25) % 25; simp)
        (by change a % p ^ 2 = r₁ % p ^ 2; rw [Nat.mod_eq_of_lt hr₁]; exact h1)
    · refine ⟨(a % 25, r₂), Finset.mem_product.mpr ⟨ha25, by simp⟩, Finset.mem_filter.mpr ⟨haI, ?_⟩⟩
      exact Nat.chineseRemainder_modEq_unique hcop (by change a % 25 = (a % 25) % 25; simp)
        (by change a % p ^ 2 = r₂ % p ^ 2; rw [Nat.mod_eq_of_lt hr₂]; exact h2)
  calc _ ≤ ((R25 ×ˢ ({r₁, r₂} : Finset ℕ)).biUnion _).card := Finset.card_le_card hsub
    _ ≤ ∑ ur ∈ R25 ×ˢ ({r₁, r₂} : Finset ℕ),
          ((Finset.Icc 1 N).filter (fun a => a % (25 * p ^ 2) =
            (Nat.chineseRemainder hcop ur.1 ur.2).val % (25 * p ^ 2))).card := Finset.card_biUnion_le
    _ ≤ ∑ _ur ∈ R25 ×ˢ ({r₁, r₂} : Finset ℕ), (N / (25 * p ^ 2) + 1) :=
          Finset.sum_le_sum fun ur _ => card_Icc_mod_eq_le N (25 * p ^ 2) _ (Nat.mul_pos (by decide) (pow_pos hp.pos 2))
    _ = (R25 ×ˢ ({r₁, r₂} : Finset ℕ)).card * (N / (25 * p ^ 2) + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 46 * (N / (25 * p ^ 2) + 1) := by
        apply Nat.mul_le_mul_right
        rw [Finset.card_product, hR25]
        have : ({r₁, r₂} : Finset ℕ).card ≤ 2 := Finset.card_le_two
        omega

private lemma card_Icc_sq_add_one_isStar_odd_le {N p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.Icc 1 N).filter (fun a => (a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ a % 2 = 1 ∧ p ^ 2 ∣ a ^ 2 + 1)).card ≤
      46 * (N / (50 * p ^ 2) + 1) := by
  obtain ⟨r₁, r₂, hr₁, hr₂, _, hroots⟩ := sq_add_one_roots_mod_p2 hp hp2
  have hcop : Nat.Coprime 50 (p ^ 2) := by
    have h2 : Nat.Coprime 2 (p ^ 2) := (Nat.prime_two.coprime_iff_not_dvd.mpr fun h =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm).pow_right 2
    have h5 : Nat.Coprime 25 (p ^ 2) := (Nat.prime_five.coprime_iff_not_dvd.mpr fun h =>
      hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp h).symm).pow 2 2
    simpa using h2.mul_left h5
  let R50 := (Finset.range 50).filter (fun u => u % 25 ≠ 7 ∧ u % 25 ≠ 18 ∧ u % 2 = 1)
  have hR50 : R50.card = 23 := by decide +kernel
  have hsub : (Finset.Icc 1 N).filter (fun a => (a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ a % 2 = 1 ∧ p ^ 2 ∣ a ^ 2 + 1) ⊆
      (R50 ×ˢ ({r₁, r₂} : Finset ℕ)).biUnion fun ur =>
        (Finset.Icc 1 N).filter (fun a => a % (50 * p ^ 2) = (Nat.chineseRemainder hcop ur.1 ur.2).val % (50 * p ^ 2)) := by
    intro a ha
    obtain ⟨haI, ⟨h7, h18⟩, hodd, hdvd⟩ := Finset.mem_filter.mp ha
    rw [Finset.mem_biUnion]
    have ha50 : a % 50 ∈ R50 := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by decide)),
      by omega, by omega, by omega⟩
    rcases hroots a hdvd with h1 | h2
    · refine ⟨(a % 50, r₁), Finset.mem_product.mpr ⟨ha50, by simp⟩, Finset.mem_filter.mpr ⟨haI, ?_⟩⟩
      exact Nat.chineseRemainder_modEq_unique hcop (by change a % 50 = (a % 50) % 50; simp)
        (by change a % p ^ 2 = r₁ % p ^ 2; rw [Nat.mod_eq_of_lt hr₁]; exact h1)
    · refine ⟨(a % 50, r₂), Finset.mem_product.mpr ⟨ha50, by simp⟩, Finset.mem_filter.mpr ⟨haI, ?_⟩⟩
      exact Nat.chineseRemainder_modEq_unique hcop (by change a % 50 = (a % 50) % 50; simp)
        (by change a % p ^ 2 = r₂ % p ^ 2; rw [Nat.mod_eq_of_lt hr₂]; exact h2)
  calc _ ≤ ((R50 ×ˢ ({r₁, r₂} : Finset ℕ)).biUnion _).card := Finset.card_le_card hsub
    _ ≤ ∑ ur ∈ R50 ×ˢ ({r₁, r₂} : Finset ℕ),
          ((Finset.Icc 1 N).filter (fun a => a % (50 * p ^ 2) =
            (Nat.chineseRemainder hcop ur.1 ur.2).val % (50 * p ^ 2))).card := Finset.card_biUnion_le
    _ ≤ ∑ _ur ∈ R50 ×ˢ ({r₁, r₂} : Finset ℕ), (N / (50 * p ^ 2) + 1) :=
          Finset.sum_le_sum fun ur _ => card_Icc_mod_eq_le N (50 * p ^ 2) _ (Nat.mul_pos (by decide) (pow_pos hp.pos 2))
    _ = (R50 ×ˢ ({r₁, r₂} : Finset ℕ)).card * (N / (50 * p ^ 2) + 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 46 * (N / (50 * p ^ 2) + 1) := by
        apply Nat.mul_le_mul_right
        rw [Finset.card_product, hR50]
        have : ({r₁, r₂} : Finset ℕ).card ≤ 2 := Finset.card_le_two
        omega

private lemma prime_mod4_of_dvd_sq_add_one {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ a ^ 2 + 1) :
    p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : ((a : ZMod p) ^ 2) = -1 := by
    have hz : ((a ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    exact eq_neg_of_add_eq_zero_left (by simpa using hz)
  have hsq : IsSquare (-1 : ZMod p) := ⟨(a : ZMod p), by rw [← sq, h1]⟩
  have hne3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp ⟨(a : ZMod p), by rw [← sq, h1]⟩
  rcases hp.eq_two_or_odd with rfl | hodd
  · exact (hp2 rfl).elim
  · omega

private lemma prime_sq_exists_sq_add_one {a : ℕ} (hstar : a % 25 ≠ 7 ∧ a % 25 ≠ 18)
    (hnsq : ¬ Squarefree (a ^ 2 + 1)) :
    ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ 13 ≤ p ∧ p ^ 2 ∣ a ^ 2 + 1 := by
  classical
  have hnot : ¬ ∀ p : ℕ, p.Prime → ¬ p * p ∣ a ^ 2 + 1 := fun h =>
    hnsq (Nat.squarefree_iff_prime_squarefree.mpr h)
  push Not at hnot
  obtain ⟨p, hp, hpp⟩ := hnot
  have hp2 : p ^ 2 ∣ a ^ 2 + 1 := by simpa [pow_two] using hpp
  have hne2 : p ≠ 2 := by
    intro h2; subst h2
    have h4 : (a ^ 2 + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd hp2
    have : a = 2 * (a / 2) + a % 2 := by omega
    have h01 : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases h01 with h0 | h1 <;> (rw [this, ‹a % 2 = _›] at h4; ring_nf at h4; omega)
  have hne5 : p ≠ 5 := by
    intro h5; subst h5
    have h25 : (a ^ 2 + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd hp2
    have hcheck : ∀ r : Fin 25, (r.val ^ 2 + 1) % 25 = 0 → r.val = 7 ∨ r.val = 18 := by decide
    have hm : ((a % 25) ^ 2 + 1) % 25 = 0 := by
      have : (a ^ 2 + 1) % 25 = ((a % 25) ^ 2 + 1) % 25 := by
        rw [Nat.add_mod, Nat.pow_mod, ← Nat.add_mod]
      omega
    rcases hcheck ⟨a % 25, Nat.mod_lt _ (by decide)⟩ hm with h7 | h18
    · exact hstar.1 h7
    · exact hstar.2 h18
  have hm4 : p % 4 = 1 := prime_mod4_of_dvd_sq_add_one hp hne2 ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hp2)
  have hp13 : 13 ≤ p := by
    have := hp.two_le
    by_contra hlt
    have : p = 5 ∨ p = 9 := by omega
    rcases this with rfl | rfl
    · exact hne5 rfl
    · exact (by decide : ¬ Nat.Prime 9) hp
  exact ⟨p, hp, hm4, hp13, hp2⟩

/-- Telescoping tail bound for `∑_{p > M} 1 / p^2`: for any finite set `Q` of integers `> M` (`M ≥ 1`),
`∑ p ∈ Q, 1 / p^2 ≤ 1 / M`. -/
private lemma sum_inv_sq_tail_le (M : ℕ) (hM : 1 ≤ M) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, M < p) :
    ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / (M : ℝ) := by
  by_cases hne : Q.Nonempty
  · let B := Q.max' hne
    have hsub : Q ⊆ Finset.Icc (M + 1) B := fun p hp =>
      Finset.mem_Icc.mpr ⟨hQ p hp, Finset.le_max' Q p hp⟩
    have h1 : ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2 ≤ ∑ k ∈ Finset.Icc (M + 1) B, (1 : ℝ) / (k : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    have h2 : ∑ k ∈ Finset.Icc (M + 1) B, (1 : ℝ) / (k : ℝ) ^ 2 ≤
        ∑ k ∈ Finset.Icc (M + 1) B, (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 : M + 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      have hkm1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 2 ≤ k by omega)
        linarith
      rw [div_sub_div _ _ hkm1_pos.ne' hk_pos.ne']
      rw [div_le_div_iff₀ (by positivity) (mul_pos hkm1_pos hk_pos)]
      nlinarith
    have h3 : ∀ B' : ℕ, M ≤ B' →
        ∑ k ∈ Finset.Icc (M + 1) B', (1 / ((k : ℝ) - 1) - 1 / (k : ℝ)) = 1 / (M : ℝ) - 1 / (B' : ℝ) := by
      intro B' hB'
      induction B', hB' using Nat.le_induction with
      | base => simp
      | succ b hb ih =>
        have hIcc : Finset.Icc (M + 1) (b + 1) = insert (b + 1) (Finset.Icc (M + 1) b) := by
          ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [hIcc, Finset.sum_insert (by simp), ih]
        push_cast; ring
    have hB_ge : M ≤ B := le_trans (Nat.le_of_lt (hQ _ (Finset.max'_mem Q hne))) le_rfl
    have h3' := h3 B hB_ge
    have hB_pos : (0 : ℝ) ≤ 1 / (B : ℝ) := by positivity
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne; rw [hne]; simp

/-- Stronger telescoping tail bound for `p ≡ 1 (mod 4)` with `p > 4 * m + 1` (`m ≥ 1`):
`∑ p ∈ Q, 1 / p^2 ≤ 1 / (16 * m)`. -/
private lemma sum_inv_sq_mod4_tail_le (m : ℕ) (hm : 1 ≤ m) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, 4 * m + 1 < p ∧ p % 4 = 1) :
    ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / (16 * (m : ℝ)) := by
  let Q' := Q.image (fun p => p / 4)
  have hinj : Set.InjOn (fun p => p / 4) (Q : Set ℕ) := by
    intro x hx y hy hxy
    have hxy' : x / 4 = y / 4 := hxy
    have hx4 := (hQ x hx).2; have hy4 := (hQ y hy).2
    omega
  have hQ'_gt : ∀ k ∈ Q', m < k := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    have hp1 := (hQ p hp).1; have hp2 := (hQ p hp).2
    have hdm := Nat.div_add_mod p 4
    omega
  have hterm : ∀ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2 ≤ (1 / 16 : ℝ) * ((1 : ℝ) / ((p / 4 : ℕ) : ℝ) ^ 2) := by
    intro p hp
    have hp1 : 4 * (p / 4) ≤ p := Nat.mul_div_le p 4
    have hpos : (0 : ℝ) < ((p / 4 : ℕ) : ℝ) := by
      have : 1 ≤ p / 4 := by have := (hQ p hp).1; omega
      exact_mod_cast this
    have h4 : 4 * ((p / 4 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    rw [show (1 / 16 : ℝ) * (1 / ((p / 4 : ℕ) : ℝ) ^ 2) = 1 / (4 * ((p / 4 : ℕ) : ℝ)) ^ 2 by ring]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) h4 2)
  calc ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ Q, (1 / 16 : ℝ) * ((1 : ℝ) / ((p / 4 : ℕ) : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = (1 / 16 : ℝ) * ∑ p ∈ Q, (1 : ℝ) / ((p / 4 : ℕ) : ℝ) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ = (1 / 16 : ℝ) * ∑ k ∈ Q', (1 : ℝ) / (k : ℝ) ^ 2 := by rw [Finset.sum_image hinj]
    _ ≤ (1 / 16 : ℝ) * (1 / (m : ℝ)) := mul_le_mul_of_nonneg_left (sum_inv_sq_tail_le m hm Q' hQ'_gt) (by norm_num)
    _ = 1 / (16 * (m : ℝ)) := by ring

-- Certified finite prime reciprocal-square sums via fast isRough43 on List.range (0.05s in decide +kernel!)
open scoped Classical in
private noncomputable irreducible_def primes1000 : Finset ℕ := (Finset.Icc 3 1000).filter Nat.Prime
open scoped Classical in
private noncomputable irreducible_def primes1000_ne (q : ℕ) : Finset ℕ := primes1000.filter (· ≠ q)
open scoped Classical in
private noncomputable irreducible_def primes2000mod4 : Finset ℕ := (Finset.Icc 13 2000).filter (fun p => Nat.Prime p ∧ p % 4 = 1)
open scoped Classical in
private noncomputable irreducible_def primes2000mod4_ge29 : Finset ℕ := primes2000mod4.filter (29 ≤ ·)

private lemma mem_primes1000 {p : ℕ} : p ∈ primes1000 ↔ 3 ≤ p ∧ p ≤ 1000 ∧ p.Prime := by
  rw [primes1000_def]; simp [and_assoc]

private lemma mem_primes1000_ne {q p : ℕ} : p ∈ primes1000_ne q ↔ 3 ≤ p ∧ p ≤ 1000 ∧ p.Prime ∧ p ≠ q := by
  rw [primes1000_ne_def]; simp [mem_primes1000, and_assoc]

private lemma mem_primes2000mod4 {p : ℕ} : p ∈ primes2000mod4 ↔ 13 ≤ p ∧ p ≤ 2000 ∧ p.Prime ∧ p % 4 = 1 := by
  rw [primes2000mod4_def]; simp [and_assoc]

private lemma mem_primes2000mod4_ge29 {p : ℕ} : p ∈ primes2000mod4_ge29 ↔ 29 ≤ p ∧ p ≤ 2000 ∧ p.Prime ∧ p % 4 = 1 := by
  rw [primes2000mod4_ge29_def]
  simp only [Finset.mem_filter, mem_primes2000mod4]
  constructor
  · rintro ⟨⟨_, h2, h3, h4⟩, h29⟩; exact ⟨h29, h2, h3, h4⟩
  · rintro ⟨h29, h2, h3, h4⟩; exact ⟨⟨by omega, h2, h3, h4⟩, h29⟩

private def isRough43 (n : ℕ) : Bool :=
  n == 2 || n == 3 || n == 5 || n == 7 || n == 11 || n == 13 || n == 17 ||
  n == 19 || n == 23 || n == 29 || n == 31 || n == 37 || n == 41 || n == 43 ||
  (decide (1 < n) && n % 2 != 0 && n % 3 != 0 && n % 5 != 0 && n % 7 != 0 &&
   n % 11 != 0 && n % 13 != 0 && n % 17 != 0 && n % 19 != 0 && n % 23 != 0 &&
   n % 29 != 0 && n % 31 != 0 && n % 37 != 0 && n % 41 != 0 && n % 43 != 0)

private lemma isRough43_of_prime {p : ℕ} (hp : p.Prime) : isRough43 p = true := by
  unfold isRough43
  by_cases h43 : p ≤ 43
  · have hcheck : ∀ x : Fin 44, x.val.Prime →
        (x.val == 2 || x.val == 3 || x.val == 5 || x.val == 7 || x.val == 11 || x.val == 13 || x.val == 17 ||
         x.val == 19 || x.val == 23 || x.val == 29 || x.val == 31 || x.val == 37 || x.val == 41 || x.val == 43) = true := by
      decide
    have h1 := hcheck ⟨p, by omega⟩ hp
    simp [h1]
  · have hnd : ∀ d : ℕ, d.Prime → d ≤ 43 → p % d ≠ 0 := fun d hd hd43 hmod => by
      have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod
      have heq : d = p := (Nat.prime_dvd_prime_iff_eq hd hp).mp hdvd
      omega
    have h1 : 1 < p := hp.one_lt
    have h2 : p % 2 = 1 := by have := hnd 2 (by decide) (by decide); omega
    have htail : (decide (1 < p) && p % 2 != 0 && p % 3 != 0 && p % 5 != 0 && p % 7 != 0 &&
        p % 11 != 0 && p % 13 != 0 && p % 17 != 0 && p % 19 != 0 && p % 23 != 0 &&
        p % 29 != 0 && p % 31 != 0 && p % 37 != 0 && p % 41 != 0 && p % 43 != 0) = true := by
      simp [h1, h2, hnd 3 (by decide) (by decide),
        hnd 5 (by decide) (by decide), hnd 7 (by decide) (by decide),
        hnd 11 (by decide) (by decide), hnd 13 (by decide) (by decide),
        hnd 17 (by decide) (by decide), hnd 19 (by decide) (by decide),
        hnd 23 (by decide) (by decide), hnd 29 (by decide) (by decide),
        hnd 31 (by decide) (by decide), hnd 37 (by decide) (by decide),
        hnd 41 (by decide) (by decide), hnd 43 (by decide) (by decide)]
    rw [htail]; simp

private lemma sum_inv_sq_of_list {P : Finset ℕ} {L : List ℕ} {B : ℕ}
    (hpos : ∀ p ∈ P, 0 < p) (hsub : ∀ p ∈ P, p ∈ L) (hnd : L.Nodup)
    (h : L.foldl (fun acc p => acc + (1000000000 / p ^ 2 + 1)) 0 ≤ B) :
    (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ (B : ℝ) / 1000000000 := by
  rw [foldl_add_eq_sum, zero_add] at h
  have hle_nat : ∑ p ∈ P, (1000000000 / p ^ 2 + 1) ≤ B := by
    calc ∑ p ∈ P, (1000000000 / p ^ 2 + 1)
        ≤ ∑ p ∈ L.toFinset, (1000000000 / p ^ 2 + 1) :=
          Finset.sum_le_sum_of_subset fun p hp => List.mem_toFinset.mpr (hsub p hp)
      _ = (L.map (fun p => 1000000000 / p ^ 2 + 1)).sum := List.sum_toFinset _ hnd
      _ ≤ B := h
  have hterm : ∀ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2 ≤ ((1000000000 / p ^ 2 + 1 : ℕ) : ℝ) / 1000000000 := by
    intro p hp
    have hp2 : 0 < p ^ 2 := pow_pos (hpos p hp) 2
    have hnat : 1000000000 < (1000000000 / p ^ 2 + 1) * p ^ 2 := by
      have := Nat.lt_div_mul_add hp2 (a := 1000000000)
      nlinarith
    have hR : (1000000000 : ℝ) ≤ ((1000000000 / p ^ 2 + 1 : ℕ) : ℝ) * (p : ℝ) ^ 2 := by
      exact_mod_cast hnat.le
    rw [div_le_div_iff₀ (by exact_mod_cast hp2) (by norm_num)]
    linarith
  calc ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ P, ((1000000000 / p ^ 2 + 1 : ℕ) : ℝ) / 1000000000 := Finset.sum_le_sum hterm
    _ = ((∑ p ∈ P, (1000000000 / p ^ 2 + 1) : ℕ) : ℝ) / 1000000000 := by
        rw [← Finset.sum_div, Nat.cast_sum]
    _ ≤ (B : ℝ) / 1000000000 := div_le_div_of_nonneg_right (by exact_mod_cast hle_nat) (by norm_num)

private def listP1000 : List ℕ := (List.range 1001).filter (fun p => decide (3 ≤ p) && isRough43 p)
private def listP2000m4 : List ℕ := (List.range 2001).filter (fun p => decide (13 ≤ p) && isRough43 p && (p % 4 == 1))

set_option maxRecDepth 8192 in
private theorem sum_primes1000_ne5_le :
    (∑ p ∈ primes1000_ne 5, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1622 / 10000 := by
  have hok : (listP1000.filter (· != 5)).foldl (fun acc p => acc + (1000000000 / p ^ 2 + 1)) 0 ≤ 162200000 := by
    decide +kernel
  have h1 := sum_inv_sq_of_list (P := primes1000_ne 5) (L := listP1000.filter (· != 5))
    (fun p hp => (mem_primes1000_ne.mp hp).2.2.1.pos)
    (fun p hp => by
      obtain ⟨h3, h1000, hpr, hne5⟩ := mem_primes1000_ne.mp hp
      exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
        by simp [h3, isRough43_of_prime hpr]⟩, by simp [hne5]⟩)
    (((List.nodup_range).filter _).filter _) hok
  linarith

set_option maxRecDepth 8192 in
private theorem sum_primes1000_ne13_le :
    (∑ p ∈ primes1000_ne 13, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1963 / 10000 := by
  have hok : (listP1000.filter (· != 13)).foldl (fun acc p => acc + (1000000000 / p ^ 2 + 1)) 0 ≤ 196300000 := by
    decide +kernel
  have h1 := sum_inv_sq_of_list (P := primes1000_ne 13) (L := listP1000.filter (· != 13))
    (fun p hp => (mem_primes1000_ne.mp hp).2.2.1.pos)
    (fun p hp => by
      obtain ⟨h3, h1000, hpr, hne13⟩ := mem_primes1000_ne.mp hp
      exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
        by simp [h3, isRough43_of_prime hpr]⟩, by simp [hne13]⟩)
    (((List.nodup_range).filter _).filter _) hok
  linarith

set_option maxRecDepth 8192 in
private theorem sum_primes1000_ne17_le :
    (∑ p ∈ primes1000_ne 17, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1987 / 10000 := by
  have hok : (listP1000.filter (· != 17)).foldl (fun acc p => acc + (1000000000 / p ^ 2 + 1)) 0 ≤ 198700000 := by
    decide +kernel
  have h1 := sum_inv_sq_of_list (P := primes1000_ne 17) (L := listP1000.filter (· != 17))
    (fun p hp => (mem_primes1000_ne.mp hp).2.2.1.pos)
    (fun p hp => by
      obtain ⟨h3, h1000, hpr, hne17⟩ := mem_primes1000_ne.mp hp
      exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
        by simp [h3, isRough43_of_prime hpr]⟩, by simp [hne17]⟩)
    (((List.nodup_range).filter _).filter _) hok
  linarith

set_option maxRecDepth 8192 in
private theorem sum_primes2000_ge29_le :
    (∑ p ∈ primes2000mod4_ge29, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 45 / 10000 := by
  have hok : (listP2000m4.filter (fun p => decide (29 ≤ p))).foldl (fun acc p => acc + (1000000000 / p ^ 2 + 1)) 0 ≤ 4500000 := by
    decide +kernel
  have h1 := sum_inv_sq_of_list (P := primes2000mod4_ge29) (L := listP2000m4.filter (fun p => decide (29 ≤ p)))
    (fun p hp => (mem_primes2000mod4_ge29.mp hp).2.2.1.pos)
    (fun p hp => by
      obtain ⟨h29, h2000, hpr, hm4⟩ := mem_primes2000mod4_ge29.mp hp
      exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
        by simp [show 13 ≤ p by omega, isRough43_of_prime hpr, hm4]⟩, by simp [h29]⟩)
    (((List.nodup_range).filter _).filter _) hok
  linarith

set_option maxRecDepth 8192 in
private theorem sum_primes2000_ge13_le :
    (∑ p ∈ primes2000mod4, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 139 / 10000 := by
  have hok : listP2000m4.foldl (fun acc p => acc + (1000000000 / p ^ 2 + 1)) 0 ≤ 13900000 := by
    decide +kernel
  have h1 := sum_inv_sq_of_list (P := primes2000mod4) (L := listP2000m4)
    (fun p hp => (mem_primes2000mod4.mp hp).2.2.1.pos)
    (fun p hp => by
      obtain ⟨h13, h2000, hpr, hm4⟩ := mem_primes2000mod4.mp hp
      exact List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
        by simp [h13, isRough43_of_prime hpr, hm4]⟩)
    ((List.nodup_range).filter _) hok
  linarith

private lemma card_primes1000 : primes1000.card ≤ 167 := by
  have hsub : primes1000 ⊆ listP1000.toFinset := fun p hp => by
    obtain ⟨h3, h1000, hpr⟩ := mem_primes1000.mp hp
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
      by simp [h3, isRough43_of_prime hpr]⟩)
  exact (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans (by decide +kernel))

private lemma card_primes2000mod4 : primes2000mod4.card ≤ 150 := by
  have hsub : primes2000mod4 ⊆ listP2000m4.toFinset := fun p hp => by
    obtain ⟨h13, h2000, hpr, hm4⟩ := mem_primes2000mod4.mp hp
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),
      by simp [h13, isRough43_of_prime hpr, hm4]⟩)
  exact (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans (by decide +kernel))

private lemma sum_nat_div_add_one_le (N k : ℕ) (P : Finset ℕ) :
    ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) ≤
      (N : ℝ) / (k : ℝ) * (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) + (P.card : ℝ) := by
  have h1 : (∑ p ∈ P, (N / (k * p ^ 2) + 1)) = (∑ p ∈ P, N / (k * p ^ 2)) + P.card := by
    simp [Finset.sum_add_distrib]
  rw [h1, Nat.cast_add, add_le_add_iff_right]
  rw [Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have hdiv : ((N / (k * p ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / ((k * p ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
  refine hdiv.trans ?_
  push_cast; rw [div_mul_div_comm, mul_one]

open scoped Classical in
/-- Bound on `a ∈ [1, N]` having `p^2 ∣ a*b + 1` for some `p > √N`, for ANY `1 ≤ b ≤ N < 1.5e9`. -/
private lemma card_ab_gt_sqrt_le {N b : ℕ} (hN_lo : 160000000 ≤ N) (hN_hi : N < 1500000000)
    (hb_pos : 0 < b) (hb_le : b ≤ N) :
    (((Finset.Icc 1 N).filter fun a => ∃ p : ℕ, p.Prime ∧ N < p ^ 2 ∧ p ^ 2 ∣ a * b + 1).card : ℝ) ≤
      (2 / 816 : ℝ) * (N : ℝ) + 25880 + 161792 := by
  let S := (Finset.Icc 1 N).filter fun a => ∃ p : ℕ, p.Prime ∧ N < p ^ 2 ∧ p ^ 2 ∣ a * b + 1
  let S_med := S.filter fun a => ∃ p : ℕ, p.Prime ∧ N < p ^ 2 ∧ 48 * p ≤ N ∧ p ^ 2 ∣ a * b + 1
  let S_hi := S.filter fun a => ∃ p : ℕ, p.Prime ∧ N < 48 * p ∧ p ^ 2 ∣ a * b + 1
  have hcov : S ⊆ S_med ∪ S_hi := by
    intro a ha
    obtain ⟨_, p, hp, hgt, hdvd⟩ := Finset.mem_filter.mp ha
    by_cases h48 : 48 * p ≤ N
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, p, hp, hgt, h48, hdvd⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha, p, hp, by omega, hdvd⟩)
  have hS_hi : S_hi.card ≤ 161792 := by
    refine large_primes_any (by omega) hN_hi hb_pos hb_le S_hi fun a ha => ?_
    obtain ⟨haS, p, _, h48, hdvd⟩ := Finset.mem_filter.mp ha
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp haS).1).2, p, h48, hdvd⟩
  let Q := (Finset.Icc 1 (N / 48)).filter fun p => p.Prime ∧ N < p ^ 2 ∧ ¬ p ∣ b
  have hS_med_sub : S_med ⊆ Q.biUnion fun p => (Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a * b + 1) := by
    intro a ha
    obtain ⟨haS, p, hp, hgt, h48, hdvd⟩ := Finset.mem_filter.mp ha
    have hpb : ¬ p ∣ b := fun h => hp.not_dvd_one
      ((Nat.dvd_add_right (dvd_mul_of_dvd_right h a)).mp ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hdvd))
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos,
      (Nat.le_div_iff_mul_le (by decide : 0 < 48)).mpr (by omega)⟩, hp, hgt, hpb⟩,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp haS).1, hdvd⟩⟩
  have hS_med_le : S_med.card ≤ Q.card := by
    calc S_med.card
        ≤ (Q.biUnion fun p => (Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a * b + 1)).card :=
          Finset.card_le_card hS_med_sub
      _ ≤ ∑ p ∈ Q, ((Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a * b + 1)).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ Q, 1 := Finset.sum_le_sum fun p hp => by
          obtain ⟨_, hpr, hgt, hpb⟩ := Finset.mem_filter.mp hp
          exact card_Icc_dvd_ab_le_one hpr hpb hgt
      _ = Q.card := by simp
  have hQ_le := prime_count_div (N := N) (K := 48) (by decide) Q
    (fun p hp => (Finset.mem_filter.mp hp).2.1)
    (fun p hp => by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      have := (Nat.le_div_iff_mul_le (by decide : 0 < 48)).mp this
      omega)
  have hS_le : S.card ≤ S_med.card + S_hi.card := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  have hQ_R : (816 : ℝ) * (Q.card : ℝ) ≤ 2 * (N : ℝ) + 816 * 25880 := by exact_mod_cast hQ_le
  have hS_R : (S.card : ℝ) ≤ (Q.card : ℝ) + 161792 := by exact_mod_cast (hS_le.trans (Nat.add_le_add hS_med_le hS_hi))
  change (S.card : ℝ) ≤ _
  linarith

set_option maxRecDepth 8192 in
open scoped Classical in
/-- Bound on `a ∈ [1, N]` having `p^2 ∣ a^2 + 1` for some `p ≡ 1 (mod 4)` with `p > 2000`. -/
private lemma card_vCount_tail_le {N : ℕ} (hN : 160000000 ≤ N) :
    (((Finset.Icc 1 N).filter fun a => ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ 2000 < p ∧ p ^ 2 ∣ a ^ 2 + 1).card : ℝ) ≤
      (1 / 3992 : ℝ) * (N : ℝ) + (2 / 2550 : ℝ) * (N : ℝ) + 25880 + 2 * (Nat.sqrt (2 * N) : ℝ) + 60000 := by
  let S := (Finset.Icc 1 N).filter fun a => ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ 2000 < p ∧ p ^ 2 ∣ a ^ 2 + 1
  let S1 := S.filter fun a => ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ 2000 < p ∧ p ^ 2 ≤ 2 * N ∧ p ^ 2 ∣ a ^ 2 + 1
  let S2 := S.filter fun a => ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ 2 * N < p ^ 2 ∧ 150 * p ≤ N ∧ p ^ 2 ∣ a ^ 2 + 1
  let S3 := S.filter fun a => ∃ p : ℕ, p.Prime ∧ N < 150 * p ∧ p ^ 2 ∣ a ^ 2 + 1
  have hcov : S ⊆ S1 ∪ (S2 ∪ S3) := by
    intro a ha
    obtain ⟨_, p, hp, hm4, h2000, hdvd⟩ := Finset.mem_filter.mp ha
    by_cases hsq : p ^ 2 ≤ 2 * N
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, p, hp, hm4, h2000, hsq, hdvd⟩)
    · by_cases h150 : 150 * p ≤ N
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨ha, p, hp, hm4, by omega, h150, hdvd⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨ha, p, hp, by omega, hdvd⟩))
  -- S1: 2000 < p ≤ sqrt(2N)
  let Q1 := (Finset.Icc 2001 (Nat.sqrt (2 * N))).filter fun p => p.Prime ∧ p % 4 = 1
  have hS1_sub : S1 ⊆ Q1.biUnion fun p => (Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a ^ 2 + 1) := by
    intro a ha
    obtain ⟨haS, p, hp, hm4, h2000, hsq, hdvd⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h2000,
      Nat.le_sqrt.mpr (by simpa [sq] using hsq)⟩, hp, hm4⟩,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp haS).1, hdvd⟩⟩
  have hS1_le : (S1.card : ℝ) ≤ (1 / 3992 : ℝ) * (N : ℝ) + 2 * (Nat.sqrt (2 * N) : ℝ) := by
    have hnat : S1.card ≤ ∑ p ∈ Q1, (2 * (N / p ^ 2 + 1)) := by
      calc S1.card ≤ (Q1.biUnion _).card := Finset.card_le_card hS1_sub
        _ ≤ ∑ p ∈ Q1, ((Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a ^ 2 + 1)).card := Finset.card_biUnion_le
        _ ≤ ∑ p ∈ Q1, 2 * (N / p ^ 2 + 1) := Finset.sum_le_sum fun p hp => by
            have hpr := (Finset.mem_filter.mp hp).2.1
            have hgt := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
            exact card_Icc_sq_add_one_le hpr (by omega)
    have hnat2 : S1.card ≤ 2 * ∑ p ∈ Q1, (N / (1 * p ^ 2) + 1) := by
      rw [Finset.mul_sum]
      exact hnat.trans_eq (Finset.sum_congr rfl fun p _ => by simp)
    have hR : (S1.card : ℝ) ≤ 2 * ((N : ℝ) / (1 : ℝ) * (∑ p ∈ Q1, (1 : ℝ) / (p : ℝ) ^ 2) + (Q1.card : ℝ)) :=
      (by exact_mod_cast hnat2 : (S1.card : ℝ) ≤ 2 * ((∑ p ∈ Q1, (N / (1 * p ^ 2) + 1) : ℕ) : ℝ)).trans
        (mul_le_mul_of_nonneg_left (by have h := sum_nat_div_add_one_le N 1 Q1; rwa [Nat.cast_one] at h) (by norm_num))
    have hsum1 : ∑ p ∈ Q1, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / (16 * (499 : ℝ)) :=
      sum_inv_sq_mod4_tail_le 499 (by decide) Q1 fun p hp =>
        ⟨by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; omega, (Finset.mem_filter.mp hp).2.2⟩
    have hQ1_card : Q1.card ≤ Nat.sqrt (2 * N) :=
      (Finset.card_filter_le _ _).trans (by rw [Nat.card_Icc]; omega)
    have hQ1_R : (Q1.card : ℝ) ≤ (Nat.sqrt (2 * N) : ℝ) := by exact_mod_cast hQ1_card
    calc (S1.card : ℝ)
        ≤ 2 * ((N : ℝ) / (1 : ℝ) * (∑ p ∈ Q1, (1 : ℝ) / (p : ℝ) ^ 2) + (Q1.card : ℝ)) := hR
      _ ≤ 2 * ((N : ℝ) / (1 : ℝ) * (1 / (16 * (499 : ℝ))) + (Nat.sqrt (2 * N) : ℝ)) := by
          gcongr
      _ = (1 / 3992 : ℝ) * (N : ℝ) + 2 * (Nat.sqrt (2 * N) : ℝ) := by ring
  -- S2: sqrt(2N) < p ≤ N/150
  let Q2 := (Finset.Icc 1 (N / 150)).filter fun p => p.Prime ∧ 2 * N < p ^ 2
  have hS2_sub : S2 ⊆ Q2.biUnion fun p => (Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a ^ 2 + 1) := by
    intro a ha
    obtain ⟨haS, p, hp, _, hgt, h150, hdvd⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos,
      (Nat.le_div_iff_mul_le (by decide : 0 < 150)).mpr (by omega)⟩, hp, hgt⟩,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp haS).1, hdvd⟩⟩
  have hS2_le : S2.card ≤ Q2.card := by
    calc S2.card ≤ (Q2.biUnion _).card := Finset.card_le_card hS2_sub
      _ ≤ ∑ p ∈ Q2, ((Finset.Icc 1 N).filter (fun a => p ^ 2 ∣ a ^ 2 + 1)).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ Q2, 1 := Finset.sum_le_sum fun p hp => by
          obtain ⟨_, hpr, hgt⟩ := Finset.mem_filter.mp hp
          exact card_Icc_sq_add_one_le_one hpr (by
            intro h2; subst h2; omega) hgt
      _ = Q2.card := by simp
  have hQ2_le := prime_count_div (N := N) (K := 150) (by decide) Q2
    (fun p hp => (Finset.mem_filter.mp hp).2.1)
    (fun p hp => by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      have := (Nat.le_div_iff_mul_le (by decide : 0 < 150)).mp this; omega)
  have hS3_le : S3.card ≤ 60000 := by
    refine large_diagonal_150 hN S3 fun a ha => ?_
    obtain ⟨haS, p, hp, h150, hdvd⟩ := Finset.mem_filter.mp ha
    exact ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp haS).1).2, p, hp, h150, hdvd⟩
  have hS_le : S.card ≤ S1.card + S2.card + S3.card := by
    have := (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
    have := Finset.card_union_le S2 S3
    omega
  have hQ2_R : (2550 : ℝ) * (Q2.card : ℝ) ≤ 2 * (N : ℝ) + 2550 * 25880 := by exact_mod_cast hQ2_le
  have hS_R : (S.card : ℝ) ≤ (S1.card : ℝ) + (Q2.card : ℝ) + 60000 := by
    exact_mod_cast (hS_le.trans (by omega))
  change (S.card : ℝ) ≤ _
  linarith

set_option maxRecDepth 8192 in
open scoped Classical in
/-- Bound on `a ∈ [1, N]` in a single residue class `r (mod m)` having `p^2 ∣ a*b + 1` for some
prime `p ≤ √N` with `p ≠ 2`, `p ≠ q_excl`, and `m` coprime to all such `p`. -/
private lemma card_ab_le_sqrt_mod_le {N m b r q_excl : ℕ} (hm : 0 < m)
    (hcop_all : ∀ p : ℕ, p.Prime → 3 ≤ p → p ≠ q_excl → Nat.Coprime m (p ^ 2))
    (B : ℝ) (hB : (∑ p ∈ primes1000_ne q_excl, (1 : ℝ) / (p : ℝ) ^ 2) ≤ B) :
    (((Finset.Icc 1 N).filter fun a => a % m = r % m ∧
      ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ q_excl ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b + 1).card : ℝ) ≤
      (N : ℝ) / (m : ℝ) * (B + 1 / 1000) + 167 + (Nat.sqrt N : ℝ) := by
  let S := (Finset.Icc 1 N).filter fun a => a % m = r % m ∧
    ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ q_excl ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b + 1
  let P1 := (primes1000_ne q_excl).filter (fun p => ¬ p ∣ b)
  let P2 := (Finset.Icc 1001 (Nat.sqrt N)).filter fun p => p.Prime ∧ p ≠ q_excl ∧ ¬ p ∣ b
  have hcov : S ⊆ (P1.biUnion fun p => (Finset.Icc 1 N).filter (fun a => a % m = r % m ∧ p ^ 2 ∣ a * b + 1)) ∪
      (P2.biUnion fun p => (Finset.Icc 1 N).filter (fun a => a % m = r % m ∧ p ^ 2 ∣ a * b + 1)) := by
    intro a ha
    obtain ⟨haI, ham, p, hp, hp3, hpne, hsq, hdvd⟩ := Finset.mem_filter.mp ha
    have hpb : ¬ p ∣ b := fun h => hp.not_dvd_one
      ((Nat.dvd_add_right (dvd_mul_of_dvd_right h a)).mp ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hdvd))
    by_cases h1000 : p ≤ 1000
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p,
        Finset.mem_filter.mpr ⟨mem_primes1000_ne.mpr ⟨hp3, h1000, hp, hpne⟩, hpb⟩,
        Finset.mem_filter.mpr ⟨haI, ham, hdvd⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, Nat.le_sqrt.mpr (by simpa [sq] using hsq)⟩, hp, hpne, hpb⟩,
        Finset.mem_filter.mpr ⟨haI, ham, hdvd⟩⟩)
  have hnat : S.card ≤ (∑ p ∈ P1, (N / (m * p ^ 2) + 1)) + ∑ p ∈ P2, (N / (m * p ^ 2) + 1) := by
    calc S.card
        ≤ (P1.biUnion fun p => (Finset.Icc 1 N).filter (fun a => a % m = r % m ∧ p ^ 2 ∣ a * b + 1)).card +
          (P2.biUnion fun p => (Finset.Icc 1 N).filter (fun a => a % m = r % m ∧ p ^ 2 ∣ a * b + 1)).card :=
          (Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
      _ ≤ (∑ p ∈ P1, ((Finset.Icc 1 N).filter (fun a => a % m = r % m ∧ p ^ 2 ∣ a * b + 1)).card) +
          (∑ p ∈ P2, ((Finset.Icc 1 N).filter (fun a => a % m = r % m ∧ p ^ 2 ∣ a * b + 1)).card) :=
          Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
      _ ≤ _ := Nat.add_le_add
          (Finset.sum_le_sum fun p hp => by
            obtain ⟨h1, hpb⟩ := Finset.mem_filter.mp hp
            obtain ⟨hp3, _, hpr, hpne⟩ := mem_primes1000_ne.mp h1
            exact card_Icc_mod_and_dvd_le hm hpr (hcop_all p hpr hp3 hpne) hpb)
          (Finset.sum_le_sum fun p hp => by
            have h1 := Finset.mem_filter.mp hp
            exact card_Icc_mod_and_dvd_le hm h1.2.1 (hcop_all p h1.2.1 (by have := (Finset.mem_Icc.mp h1.1).1; omega) h1.2.2.1) h1.2.2.2)
  have hR1 := sum_nat_div_add_one_le N m P1
  have hR2 := sum_nat_div_add_one_le N m P2
  have hsum1 : ∑ p ∈ P1, (1 : ℝ) / (p : ℝ) ^ 2 ≤ B :=
    (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.mp hp).1) fun _ _ _ => by positivity).trans hB
  have hsum2 : ∑ p ∈ P2, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / (1000 : ℝ) :=
    sum_inv_sq_tail_le 1000 (by decide) P2 fun p hp => by
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; omega
  have hP1_card : (P1.card : ℝ) ≤ 167 := by
    have hsub1 : P1 ⊆ primes1000 := fun p hp => by
      obtain ⟨h3, h1000, hpr, _⟩ := mem_primes1000_ne.mp (Finset.mem_filter.mp hp).1
      exact mem_primes1000.mpr ⟨h3, h1000, hpr⟩
    exact_mod_cast (Finset.card_le_card hsub1).trans card_primes1000
  have hP2_card : (P2.card : ℝ) ≤ (Nat.sqrt N : ℝ) := by
    have : P2.card ≤ Nat.sqrt N := (Finset.card_filter_le _ _).trans (by rw [Nat.card_Icc]; omega)
    exact_mod_cast this
  have hS_R : (S.card : ℝ) ≤ ((∑ p ∈ P1, (N / (m * p ^ 2) + 1) : ℕ) : ℝ) +
      ((∑ p ∈ P2, (N / (m * p ^ 2) + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
  have hNm : 0 ≤ (N : ℝ) / (m : ℝ) := by positivity
  change (S.card : ℝ) ≤ _
  nlinarith

/- ### Section 5: Final Assembly of Part 1 and Part 2 -/

private lemma c7_lower (N : ℕ) : (N : ℝ) / 25 - 1 ≤ (((Finset.Icc 1 N).filter (fun a => a % 25 = 7)).card : ℝ) := by
  have hsub : (Finset.range ((N + 18) / 25)).image (fun k => 25 * k + 7) ⊆
      (Finset.Icc 1 N).filter (fun a => a % 25 = 7) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    have hk' := Finset.mem_range.mp hk
    have hle : 25 * k + 7 ≤ N := by
      have := Nat.mul_le_of_le_div 25 (k + 1) (N + 18) (by omega)
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hle⟩, by omega⟩
  have hinj : Function.Injective (fun k : ℕ => 25 * k + 7) := fun a b h => by dsimp only at h; omega
  have hcard : (N + 18) / 25 ≤ ((Finset.Icc 1 N).filter (fun a => a % 25 = 7)).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hinj, Finset.card_range] at this
  have hdiv : (N : ℝ) / 25 - 1 ≤ (((N + 18) / 25 : ℕ) : ℝ) := by
    have : N ≤ 25 * ((N + 18) / 25) + 6 := by omega
    have hR : (N : ℝ) ≤ 25 * (((N + 18) / 25 : ℕ) : ℝ) + 6 := by exact_mod_cast this
    linarith
  exact hdiv.trans (by exact_mod_cast hcard)

private lemma not_dvd_25_ab {a b : ℕ} (ha : a % 25 = 7 ∨ a % 25 = 18)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) : ¬ 25 ∣ a * b + 1 := by
  intro h
  have hm : (a * b + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd h
  have h2 : ((a % 25) * (b % 25) + 1) % 25 = 0 := by
    rw [Nat.add_mod, Nat.mul_mod] at hm
    simpa [Nat.add_mod] using hm
  have hcheck : ∀ u v : Fin 25, (u.val = 7 ∨ u.val = 18) → (u.val * v.val + 1) % 25 = 0 →
      v.val = 7 ∨ v.val = 18 := by decide
  rcases hcheck ⟨a % 25, Nat.mod_lt _ (by decide)⟩ ⟨b % 25, Nat.mod_lt _ (by decide)⟩ ha h2 with h7 | h18
  · exact hb.1 h7
  · exact hb.2 h18

private lemma sq_add_one_mod169 {a : ℕ} (h : 13 ^ 2 ∣ a ^ 2 + 1) :
    a % 169 = 70 ∨ a % 169 = 99 := by
  have hm : ((a % 169) ^ 2 + 1) % 169 = 0 := by
    have : (a ^ 2 + 1) % 169 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.add_mod, Nat.pow_mod, ← Nat.add_mod] at this; exact this
  have hcheck : ∀ r : Fin 169, (r.val ^ 2 + 1) % 169 = 0 → r.val = 70 ∨ r.val = 99 := by decide +kernel
  exact hcheck ⟨a % 169, Nat.mod_lt _ (by decide)⟩ hm

private lemma sq_add_one_mod289 {a : ℕ} (h : 17 ^ 2 ∣ a ^ 2 + 1) :
    a % 289 = 38 ∨ a % 289 = 251 := by
  have hm : ((a % 289) ^ 2 + 1) % 289 = 0 := by
    have : (a ^ 2 + 1) % 289 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.add_mod, Nat.pow_mod, ← Nat.add_mod] at this; exact this
  have hcheck : ∀ r : Fin 289, (r.val ^ 2 + 1) % 289 = 0 → r.val = 38 ∨ r.val = 251 := by decide +kernel
  exact hcheck ⟨a % 289, Nat.mod_lt _ (by decide)⟩ hm

private lemma dvd_ab_and_sq_same_prime {a b q : ℕ} (hq : q.Prime) (h1 : q ^ 2 ∣ a ^ 2 + 1)
    (h2 : q ^ 2 ∣ a * b + 1) : a % q ^ 2 = b % q ^ 2 := by
  have hqa : ¬ q ∣ a := fun h => hq.not_dvd_one
    ((Nat.dvd_add_right (dvd_pow h (by decide : 2 ≠ 0))).mp ((dvd_pow_self q (by decide : 2 ≠ 0)).trans h1))
  have hcop : Nat.Coprime a (q ^ 2) := hq.coprime_pow_of_not_dvd (m := 2) hqa
  have hdiff : (q ^ 2 : ℤ) ∣ (a : ℤ) * ((a : ℤ) - (b : ℤ)) := by
    have h1' : (q ^ 2 : ℤ) ∣ (a : ℤ) ^ 2 + 1 := by exact_mod_cast h1
    have h2' : (q ^ 2 : ℤ) ∣ (a : ℤ) * (b : ℤ) + 1 := by exact_mod_cast h2
    have hsub := dvd_sub h1' h2'
    rwa [show ((a : ℤ) ^ 2 + 1) - ((a : ℤ) * (b : ℤ) + 1) = (a : ℤ) * ((a : ℤ) - (b : ℤ)) by ring] at hsub
  have hcopZ : IsCoprime (a : ℤ) (q ^ 2 : ℤ) := by exact_mod_cast hcop.isCoprime
  have hdvd : (q ^ 2 : ℤ) ∣ (a : ℤ) - (b : ℤ) := hcopZ.symm.dvd_of_dvd_mul_left hdiff
  have hmod : (a : ℤ) % (q ^ 2 : ℤ) = (b : ℤ) % (q ^ 2 : ℤ) :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hdvd)
  exact_mod_cast hmod

private lemma card_Icc_isStar_and_mod_le {N m r : ℕ} (hm : 0 < m) (hcop : Nat.Coprime 25 m) :
    ((Finset.Icc 1 N).filter (fun a => (a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ a % m = r % m)).card ≤
      23 * (N / (25 * m) + 1) := by
  let R25 := (Finset.range 25).filter (fun u => u ≠ 7 ∧ u ≠ 18)
  have hR25 : R25.card = 23 := by decide +kernel
  have hsub : (Finset.Icc 1 N).filter (fun a => (a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ a % m = r % m) ⊆
      R25.biUnion fun u =>
        (Finset.Icc 1 N).filter (fun a => a % (25 * m) = (Nat.chineseRemainder hcop u r).val % (25 * m)) := by
    intro a ha
    obtain ⟨haI, ⟨h7, h18⟩, ham⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_biUnion.mpr ⟨a % 25,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by decide)), h7, h18⟩,
      Finset.mem_filter.mpr ⟨haI, Nat.chineseRemainder_modEq_unique hcop
        (by change a % 25 = (a % 25) % 25; simp) ham⟩⟩
  calc _ ≤ (R25.biUnion _).card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ R25, ((Finset.Icc 1 N).filter (fun a => a % (25 * m) =
          (Nat.chineseRemainder hcop u r).val % (25 * m))).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ R25, (N / (25 * m) + 1) := Finset.sum_le_sum fun u _ =>
          card_Icc_mod_eq_le N (25 * m) _ (Nat.mul_pos (by decide) hm)
    _ = 23 * (N / (25 * m) + 1) := by rw [Finset.sum_const, hR25, smul_eq_mul]

private lemma sqrt_bound_of_ge {N : ℕ} (hN : 160000000 ≤ N) :
    (Nat.sqrt N : ℝ) ≤ (N : ℝ) / 12000 ∧ (Nat.sqrt (2 * N) : ℝ) ≤ (N : ℝ) / 8000 := by
  have h1 : Nat.sqrt N * 12000 ≤ N := by
    have hsq := Nat.sqrt_le N
    have : (Nat.sqrt N * 12000) ^ 2 ≤ N * N := by nlinarith
    nlinarith
  have h2 : Nat.sqrt (2 * N) * 8000 ≤ N := by
    have hsq := Nat.sqrt_le (2 * N)
    have : (Nat.sqrt (2 * N) * 8000) ^ 2 ≤ N * N := by nlinarith
    nlinarith
  have h1R : (Nat.sqrt N : ℝ) * 12000 ≤ (N : ℝ) := by exact_mod_cast h1
  have h2R : (Nat.sqrt (2 * N) : ℝ) * 8000 ≤ (N : ℝ) := by exact_mod_cast h2
  exact ⟨by linarith, by linarith⟩

end OMA.P_Erdos848_H3_R1_H1

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8192 in
theorem OMA.solution : OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1_H3_R1.H1 := by
  classical
  intro N hN_lo hN_hi
  dsimp only
  have hNR : (160000000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_lo
  have ⟨hsqN, hsq2N⟩ := OMA.P_Erdos848_H3_R1_H1.sqrt_bound_of_ge hN_lo
  have hc7 := OMA.P_Erdos848_H3_R1_H1.c7_lower N
  have hv_tail := OMA.P_Erdos848_H3_R1_H1.card_vCount_tail_le hN_lo
  constructor
  · -- Part 1: b even, IsStar b
    intro b hb_wit hb_star hb_even
    have hb_pos : 0 < b := (Finset.mem_Icc.mp hb_wit.1).1
    have hb_le : b ≤ N := (Finset.mem_Icc.mp hb_wit.1).2
    let Bad := (Finset.Icc 1 N).filter (fun a => (a % 25 = 7 ∨ a % 25 = 18) ∧ ¬ Squarefree (a * b + 1))
    let LemC := (Finset.Icc 1 N).filter (fun a => (a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ ¬ Squarefree (a * a + 1) ∧ ¬ Squarefree (a * b + 1))
    -- Note Bad and LemC are disjoint! So Bad.card + LemC.card = (Bad ∪ LemC).card
    have hdisj : Disjoint Bad LemC := Finset.disjoint_filter.mpr fun a _ h1 h2 => by
      rcases h1.1 with h7 | h18
      · exact h2.1.1 h7
      · exact h2.1.2 h18
    -- Decompose Bad ∪ LemC into:
    -- (1) A_hi: p > sqrt(N) dividing a*b + 1 (shared!)
    -- (2) B7, B18: a % 25 = 7 or 18, p ≤ sqrt(N), p ≥ 3, p ≠ 5, p^2 | a*b + 1
    -- (3) L13_same: IsStar a ∧ a % 169 = b % 169
    -- (4) L13_other: a % 169 ∈ {70, 99}, p ≤ sqrt(N), p ≥ 3, p ≠ 13, p^2 | a*b + 1
    -- (5) L17_same: IsStar a ∧ a % 289 = b % 289
    -- (6) L17_other: a % 289 ∈ {38, 251}, p ≤ sqrt(N), p ≥ 3, p ≠ 17, p^2 | a*b + 1
    -- (7) V_sm29: IsStar a ∧ ∃ p ∈ primes2000mod4.filter (29 ≤ ·), p^2 | a^2 + 1
    -- (8) V_tail: ∃ p.Prime, p % 4 = 1, 2000 < p, p^2 | a^2 + 1
    let A_hi := (Finset.Icc 1 N).filter fun a => ∃ p : ℕ, p.Prime ∧ N < p ^ 2 ∧ p ^ 2 ∣ a * b + 1
    let B7 := (Finset.Icc 1 N).filter fun a => a % 25 = 7 % 25 ∧
      ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ 5 ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b + 1
    let B18 := (Finset.Icc 1 N).filter fun a => a % 25 = 18 % 25 ∧
      ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ 5 ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b + 1
    let L13_same := (Finset.Icc 1 N).filter fun a => (a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ a % 169 = b % 169
    let L13_70 := (Finset.Icc 1 N).filter fun a => a % 169 = 70 % 169 ∧
      ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ 13 ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b + 1
    let L13_99 := (Finset.Icc 1 N).filter fun a => a % 169 = 99 % 169 ∧
      ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ 13 ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b + 1
    let L17_same := (Finset.Icc 1 N).filter fun a => (a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ a % 289 = b % 289
    let L17_38 := (Finset.Icc 1 N).filter fun a => a % 289 = 38 % 289 ∧
      ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ 17 ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b + 1
    let L17_251 := (Finset.Icc 1 N).filter fun a => a % 289 = 251 % 289 ∧
      ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ 17 ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b + 1
    let V_sm29 := OMA.P_Erdos848_H3_R1_H1.primes2000mod4_ge29.biUnion fun p =>
      (Finset.Icc 1 N).filter fun a => (a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ p ^ 2 ∣ a ^ 2 + 1
    let V_tail := (Finset.Icc 1 N).filter fun a => ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ 2000 < p ∧ p ^ 2 ∣ a ^ 2 + 1
    have hprime_ab : ∀ a, ¬ Squarefree (a * b + 1) → ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ^ 2 ∣ a * b + 1 := by
      intro a hnsq
      have hnot : ¬ ∀ p : ℕ, p.Prime → ¬ p * p ∣ a * b + 1 := fun h =>
        hnsq (Nat.squarefree_iff_prime_squarefree.mpr h)
      push Not at hnot
      obtain ⟨p, hp, hpp⟩ := hnot
      have hp2 : p ^ 2 ∣ a * b + 1 := by simpa [pow_two] using hpp
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        by_contra hlt
        have hp2_eq : p = 2 := by omega
        subst hp2_eq
        have h4 : 2 ∣ a * b + 1 := (dvd_pow_self 2 (by decide : 2 ≠ 0)).trans hp2
        have : (a * b + 1) % 2 = 1 := by rw [Nat.add_mod, Nat.mul_mod, hb_even]; simp
        have : (a * b + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h4
        omega
      exact ⟨p, hp, hp3, hp2⟩
    have hcov : Bad ∪ LemC ⊆ A_hi ∪ (B7 ∪ (B18 ∪ (L13_same ∪ (L13_70 ∪ (L13_99 ∪ (L17_same ∪ (L17_38 ∪ (L17_251 ∪ (V_sm29 ∪ V_tail))))))))) := by
      intro a ha
      rcases Finset.mem_union.mp ha with haB | haL
      · obtain ⟨haI, ha25, hnsq⟩ := Finset.mem_filter.mp haB
        obtain ⟨p, hp, hp3, hp2⟩ := hprime_ab a hnsq
        by_cases hgt : N < p ^ 2
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haI, p, hp, hgt, hp2⟩)
        · have hp5 : p ≠ 5 := by
            intro h5; subst h5
            exact OMA.P_Erdos848_H3_R1_H1.not_dvd_25_ab ha25 hb_star (by simpa using hp2)
          rcases ha25 with h7 | h18
          · exact Finset.mem_union_right _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨haI, h7, p, hp, hp3, hp5, by omega, hp2⟩))
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
              (Finset.mem_filter.mpr ⟨haI, h18, p, hp, hp3, hp5, by omega, hp2⟩)))
      · obtain ⟨haI, hstar, hnsq_a, hnsq_ab⟩ := Finset.mem_filter.mp haL
        have hnsq_a' : ¬ Squarefree (a ^ 2 + 1) := by simpa [sq] using hnsq_a
        obtain ⟨q, hq, hqm4, hq13, hq2⟩ := OMA.P_Erdos848_H3_R1_H1.prime_sq_exists_sq_add_one hstar hnsq_a'
        by_cases hq13_eq : q = 13
        · subst hq13_eq
          obtain ⟨p, hp, hp3, hp2⟩ := hprime_ab a hnsq_ab
          by_cases hgt : N < p ^ 2
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haI, p, hp, hgt, hp2⟩)
          · by_cases hp13 : p = 13
            · subst hp13
              have hsame := OMA.P_Erdos848_H3_R1_H1.dvd_ab_and_sq_same_prime (by decide : Nat.Prime 13) hq2 hp2
              exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haI, hstar, hsame⟩))))
            · rcases OMA.P_Erdos848_H3_R1_H1.sq_add_one_mod169 hq2 with h70 | h99
              · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                  (Finset.mem_union_right _ (Finset.mem_union_left _
                    (Finset.mem_filter.mpr ⟨haI, h70, p, hp, hp3, hp13, by omega, hp2⟩)))))
              · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                  (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
                    (Finset.mem_filter.mpr ⟨haI, h99, p, hp, hp3, hp13, by omega, hp2⟩))))))
        · by_cases hq17_eq : q = 17
          · subst hq17_eq
            obtain ⟨p, hp, hp3, hp2⟩ := hprime_ab a hnsq_ab
            by_cases hgt : N < p ^ 2
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haI, p, hp, hgt, hp2⟩)
            · by_cases hp17 : p = 17
              · subst hp17
                have hsame := OMA.P_Erdos848_H3_R1_H1.dvd_ab_and_sq_same_prime (by decide : Nat.Prime 17) hq2 hp2
                exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                  (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                    (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haI, hstar, hsame⟩)))))))
              · rcases OMA.P_Erdos848_H3_R1_H1.sq_add_one_mod289 hq2 with h38 | h251
                · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                    (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                      (Finset.mem_union_right _ (Finset.mem_union_left _
                        (Finset.mem_filter.mpr ⟨haI, h38, p, hp, hp3, hp17, by omega, hp2⟩))))))))
                · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                    (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                      (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _
                        (Finset.mem_filter.mpr ⟨haI, h251, p, hp, hp3, hp17, by omega, hp2⟩)))))))))
          · have hq29 : 29 ≤ q := by
              by_contra hlt
              have hcases : q = 21 ∨ q = 25 := by omega
              rcases hcases with rfl | rfl
              · exact (by decide : ¬ Nat.Prime 21) hq
              · exact (by decide : ¬ Nat.Prime 25) hq
            by_cases hq2000 : q ≤ 2000
            · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                  (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                    (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q,
                      OMA.P_Erdos848_H3_R1_H1.mem_primes2000mod4_ge29.mpr ⟨hq29, hq2000, hq, hqm4⟩,
                      Finset.mem_filter.mpr ⟨haI, hstar, hq2⟩⟩))))))))))
            · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                  (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_right _
                    (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haI, q, hq, hqm4, by omega, hq2⟩))))))))))
    have hcard_sum : Bad.card + LemC.card ≤
        A_hi.card + B7.card + B18.card + L13_same.card + L13_70.card + L13_99.card +
        L17_same.card + L17_38.card + L17_251.card + V_sm29.card + V_tail.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      have h1 := Finset.card_le_card hcov
      have := Finset.card_union_le A_hi (B7 ∪ (B18 ∪ (L13_same ∪ (L13_70 ∪ (L13_99 ∪ (L17_same ∪ (L17_38 ∪ (L17_251 ∪ (V_sm29 ∪ V_tail)))))))))
      have := Finset.card_union_le B7 (B18 ∪ (L13_same ∪ (L13_70 ∪ (L13_99 ∪ (L17_same ∪ (L17_38 ∪ (L17_251 ∪ (V_sm29 ∪ V_tail))))))))
      have := Finset.card_union_le B18 (L13_same ∪ (L13_70 ∪ (L13_99 ∪ (L17_same ∪ (L17_38 ∪ (L17_251 ∪ (V_sm29 ∪ V_tail)))))))
      have := Finset.card_union_le L13_same (L13_70 ∪ (L13_99 ∪ (L17_same ∪ (L17_38 ∪ (L17_251 ∪ (V_sm29 ∪ V_tail))))))
      have := Finset.card_union_le L13_70 (L13_99 ∪ (L17_same ∪ (L17_38 ∪ (L17_251 ∪ (V_sm29 ∪ V_tail)))))
      have := Finset.card_union_le L13_99 (L17_same ∪ (L17_38 ∪ (L17_251 ∪ (V_sm29 ∪ V_tail))))
      have := Finset.card_union_le L17_same (L17_38 ∪ (L17_251 ∪ (V_sm29 ∪ V_tail)))
      have := Finset.card_union_le L17_38 (L17_251 ∪ (V_sm29 ∪ V_tail))
      have := Finset.card_union_le L17_251 (V_sm29 ∪ V_tail)
      have := Finset.card_union_le V_sm29 V_tail
      omega
    -- Bound each term in ℝ
    have hA_hi := OMA.P_Erdos848_H3_R1_H1.card_ab_gt_sqrt_le hN_lo hN_hi hb_pos hb_le
    have hcop25 : ∀ p : ℕ, p.Prime → 3 ≤ p → p ≠ 5 → Nat.Coprime 25 (p ^ 2) := fun p hp _ h5 =>
      (Nat.prime_five.coprime_iff_not_dvd.mpr fun h =>
        h5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp h).symm).pow 2 2
    have hcop169 : ∀ p : ℕ, p.Prime → 3 ≤ p → p ≠ 13 → Nat.Coprime 169 (p ^ 2) := fun p hp _ h13 =>
      ((by decide : Nat.Prime 13).coprime_iff_not_dvd.mpr fun h =>
        h13 ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp h).symm).pow 2 2
    have hcop289 : ∀ p : ℕ, p.Prime → 3 ≤ p → p ≠ 17 → Nat.Coprime 289 (p ^ 2) := fun p hp _ h17 =>
      ((by decide : Nat.Prime 17).coprime_iff_not_dvd.mpr fun h =>
        h17 ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp h).symm).pow 2 2
    have hB7 := OMA.P_Erdos848_H3_R1_H1.card_ab_le_sqrt_mod_le (N := N) (m := 25) (b := b) (r := 7) (q_excl := 5)
      (by decide) hcop25 _ OMA.P_Erdos848_H3_R1_H1.sum_primes1000_ne5_le
    have hB18 := OMA.P_Erdos848_H3_R1_H1.card_ab_le_sqrt_mod_le (N := N) (m := 25) (b := b) (r := 18) (q_excl := 5)
      (by decide) hcop25 _ OMA.P_Erdos848_H3_R1_H1.sum_primes1000_ne5_le
    have hL13_70 := OMA.P_Erdos848_H3_R1_H1.card_ab_le_sqrt_mod_le (N := N) (m := 169) (b := b) (r := 70) (q_excl := 13)
      (by decide) hcop169 _ OMA.P_Erdos848_H3_R1_H1.sum_primes1000_ne13_le
    have hL13_99 := OMA.P_Erdos848_H3_R1_H1.card_ab_le_sqrt_mod_le (N := N) (m := 169) (b := b) (r := 99) (q_excl := 13)
      (by decide) hcop169 _ OMA.P_Erdos848_H3_R1_H1.sum_primes1000_ne13_le
    have hL17_38 := OMA.P_Erdos848_H3_R1_H1.card_ab_le_sqrt_mod_le (N := N) (m := 289) (b := b) (r := 38) (q_excl := 17)
      (by decide) hcop289 _ OMA.P_Erdos848_H3_R1_H1.sum_primes1000_ne17_le
    have hL17_251 := OMA.P_Erdos848_H3_R1_H1.card_ab_le_sqrt_mod_le (N := N) (m := 289) (b := b) (r := 251) (q_excl := 17)
      (by decide) hcop289 _ OMA.P_Erdos848_H3_R1_H1.sum_primes1000_ne17_le
    have hL13_same : (L13_same.card : ℝ) ≤ 23 * ((N : ℝ) / 4225 + 1) := by
      have hnat := OMA.P_Erdos848_H3_R1_H1.card_Icc_isStar_and_mod_le (N := N) (m := 169) (r := b) (by decide) (by decide)
      have hR : (L13_same.card : ℝ) ≤ 23 * (((N / 4225 : ℕ) : ℝ) + 1) := by exact_mod_cast hnat
      have hdiv : ((N / 4225 : ℕ) : ℝ) ≤ (N : ℝ) / 4225 := Nat.cast_div_le
      linarith
    have hL17_same : (L17_same.card : ℝ) ≤ 23 * ((N : ℝ) / 7225 + 1) := by
      have hnat := OMA.P_Erdos848_H3_R1_H1.card_Icc_isStar_and_mod_le (N := N) (m := 289) (r := b) (by decide) (by decide)
      have hR : (L17_same.card : ℝ) ≤ 23 * (((N / 7225 : ℕ) : ℝ) + 1) := by exact_mod_cast hnat
      have hdiv : ((N / 7225 : ℕ) : ℝ) ≤ (N : ℝ) / 7225 := Nat.cast_div_le
      linarith
    have hV_sm29 : (V_sm29.card : ℝ) ≤ 46 * ((N : ℝ) / 25 * (45 / 10000 : ℝ) + 150) := by
      let P29 := OMA.P_Erdos848_H3_R1_H1.primes2000mod4_ge29
      have hnat : V_sm29.card ≤ 46 * ∑ p ∈ P29, (N / (25 * p ^ 2) + 1) := by
        rw [Finset.mul_sum]
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p hp => ?_)
        obtain ⟨h29, _, hpr, _⟩ := OMA.P_Erdos848_H3_R1_H1.mem_primes2000mod4_ge29.mp hp
        exact OMA.P_Erdos848_H3_R1_H1.card_Icc_sq_add_one_isStar_le hpr (by omega) (by omega)
      have hR1 := OMA.P_Erdos848_H3_R1_H1.sum_nat_div_add_one_le N 25 P29
      have hsum := OMA.P_Erdos848_H3_R1_H1.sum_primes2000_ge29_le
      have hP29_card : (P29.card : ℝ) ≤ 150 := by
        have hsub : P29 ⊆ OMA.P_Erdos848_H3_R1_H1.primes2000mod4 := fun p hp => by
          obtain ⟨h29, h2000, hpr, hm4⟩ := OMA.P_Erdos848_H3_R1_H1.mem_primes2000mod4_ge29.mp hp
          exact OMA.P_Erdos848_H3_R1_H1.mem_primes2000mod4.mpr ⟨by omega, h2000, hpr, hm4⟩
        exact_mod_cast (Finset.card_le_card hsub).trans OMA.P_Erdos848_H3_R1_H1.card_primes2000mod4
      have hnatR : (V_sm29.card : ℝ) ≤ 46 * ((∑ p ∈ P29, (N / (25 * p ^ 2) + 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      simp only [Nat.cast_ofNat] at hR1
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    have htotR : (Bad.card : ℝ) + (LemC.card : ℝ) ≤
        (A_hi.card : ℝ) + (B7.card : ℝ) + (B18.card : ℝ) + (L13_same.card : ℝ) +
        (L13_70.card : ℝ) + (L13_99.card : ℝ) + (L17_same.card : ℝ) + (L17_38.card : ℝ) +
        (L17_251.card : ℝ) + (V_sm29.card : ℝ) + (V_tail.card : ℝ) := by exact_mod_cast hcard_sum
    have hle_R : (Bad.card : ℝ) + (LemC.card : ℝ) ≤ (((Finset.Icc 1 N).filter (fun a => a % 25 = 7)).card : ℝ) := by
      norm_num at hB7 hB18 hL13_70 hL13_99 hL17_38 hL17_251
      linarith
    exact_mod_cast hle_R
  · -- Part 2: b₁ % 4 = 1, b₃ % 4 = 3, both IsStar
    intro b₁ b₃ hb₁_wit hb₁_star hb₁_m4 hb₃_wit hb₃_star hb₃_m4
    have hb₁_pos : 0 < b₁ := (Finset.mem_Icc.mp hb₁_wit.1).1
    have hb₁_le : b₁ ≤ N := (Finset.mem_Icc.mp hb₁_wit.1).2
    have hb₃_pos : 0 < b₃ := (Finset.mem_Icc.mp hb₃_wit.1).1
    have hb₃_le : b₃ ≤ N := (Finset.mem_Icc.mp hb₃_wit.1).2
    let Bad1 := (Finset.Icc 1 N).filter (fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ (a % 4 = 1 ∨ a % 2 = 0)) ∧ ¬ Squarefree (a * b₁ + 1))
    let Bad3 := (Finset.Icc 1 N).filter (fun a => ((a % 25 = 7 ∨ a % 25 = 18) ∧ a % 4 = 3) ∧ ¬ Squarefree (a * b₃ + 1))
    let Vodd := (Finset.Icc 1 N).filter (fun a => ((a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ a % 2 = 1) ∧ ¬ Squarefree (a * a + 1))
    -- For Bad1: a % 100 takes 6 values: {7, 18, 32, 43, 57, 68, 82, 93} minus those ≡ 3 (mod 4) = {7, 43} -> {18, 32, 57, 68, 82, 93} (6 values!)
    -- For Bad3: a % 100 takes 2 values: {7, 43} (2 values!)
    have hcop100 : ∀ p : ℕ, p.Prime → 3 ≤ p → p ≠ 5 → Nat.Coprime 100 (p ^ 2) := fun p hp hp3 h5 => by
      have h2 : Nat.Coprime 4 (p ^ 2) := (Nat.prime_two.coprime_iff_not_dvd.mpr fun h => by
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h; omega).pow 2 2
      have h5' : Nat.Coprime 25 (p ^ 2) := (Nat.prime_five.coprime_iff_not_dvd.mpr fun h =>
        h5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp h).symm).pow 2 2
      simpa using h2.mul_left h5'
    let A1_hi := (Finset.Icc 1 N).filter fun a => ∃ p : ℕ, p.Prime ∧ N < p ^ 2 ∧ p ^ 2 ∣ a * b₁ + 1
    let A3_hi := (Finset.Icc 1 N).filter fun a => ∃ p : ℕ, p.Prime ∧ N < p ^ 2 ∧ p ^ 2 ∣ a * b₃ + 1
    let R1 : Finset ℕ := {18, 32, 57, 68, 82, 93}
    let R3 : Finset ℕ := {7, 43}
    let B1_sm := R1.biUnion fun r => (Finset.Icc 1 N).filter fun a => a % 100 = r % 100 ∧
      ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ 5 ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b₁ + 1
    let B3_sm := R3.biUnion fun r => (Finset.Icc 1 N).filter fun a => a % 100 = r % 100 ∧
      ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ 5 ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b₃ + 1
    let V_sm13 := OMA.P_Erdos848_H3_R1_H1.primes2000mod4.biUnion fun p =>
      (Finset.Icc 1 N).filter fun a => (a % 25 ≠ 7 ∧ a % 25 ≠ 18) ∧ a % 2 = 1 ∧ p ^ 2 ∣ a ^ 2 + 1
    let V_tail := (Finset.Icc 1 N).filter fun a => ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ 2000 < p ∧ p ^ 2 ∣ a ^ 2 + 1
    have hcov1 : Bad1 ⊆ A1_hi ∪ B1_sm := by
      intro a ha
      obtain ⟨haI, ⟨ha25, ha4⟩, hnsq⟩ := Finset.mem_filter.mp ha
      have hnot : ¬ ∀ p : ℕ, p.Prime → ¬ p * p ∣ a * b₁ + 1 := fun h =>
        hnsq (Nat.squarefree_iff_prime_squarefree.mpr h)
      push Not at hnot
      obtain ⟨p, hp, hpp⟩ := hnot
      have hp2 : p ^ 2 ∣ a * b₁ + 1 := by simpa [pow_two] using hpp
      by_cases hgt : N < p ^ 2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haI, p, hp, hgt, hp2⟩)
      · have hp3 : 3 ≤ p := by
          have := hp.two_le
          by_contra hlt
          have : p = 2 := by omega
          subst this
          have h4 : (a * b₁ + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd hp2
          have h4' : ((a % 4) * (b₁ % 4) + 1) % 4 = 0 := by
            rw [Nat.add_mod, Nat.mul_mod] at h4
            simpa [Nat.add_mod] using h4
          rw [hb₁_m4] at h4'
          omega
        have hp5 : p ≠ 5 := by
          intro h5; subst h5
          exact OMA.P_Erdos848_H3_R1_H1.not_dvd_25_ab ha25 hb₁_star (by simpa using hp2)
        have ha100 : a % 100 ∈ R1 := by
          have : a % 100 = 18 ∨ a % 100 = 32 ∨ a % 100 = 57 ∨ a % 100 = 68 ∨ a % 100 = 82 ∨ a % 100 = 93 := by omega
          rcases this with h | h | h | h | h | h <;> simp [R1, h]
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a % 100, ha100,
          Finset.mem_filter.mpr ⟨haI, by simp, p, hp, hp3, hp5, by omega, hp2⟩⟩)
    have hcov3 : Bad3 ⊆ A3_hi ∪ B3_sm := by
      intro a ha
      obtain ⟨haI, ⟨ha25, ha4⟩, hnsq⟩ := Finset.mem_filter.mp ha
      have hnot : ¬ ∀ p : ℕ, p.Prime → ¬ p * p ∣ a * b₃ + 1 := fun h =>
        hnsq (Nat.squarefree_iff_prime_squarefree.mpr h)
      push Not at hnot
      obtain ⟨p, hp, hpp⟩ := hnot
      have hp2 : p ^ 2 ∣ a * b₃ + 1 := by simpa [pow_two] using hpp
      by_cases hgt : N < p ^ 2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨haI, p, hp, hgt, hp2⟩)
      · have hp3 : 3 ≤ p := by
          have := hp.two_le
          by_contra hlt
          have : p = 2 := by omega
          subst this
          have h4 : (a * b₃ + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd hp2
          have h4' : ((a % 4) * (b₃ % 4) + 1) % 4 = 0 := by
            rw [Nat.add_mod, Nat.mul_mod] at h4
            simpa [Nat.add_mod] using h4
          rw [ha4, hb₃_m4] at h4'
          omega
        have hp5 : p ≠ 5 := by
          intro h5; subst h5
          exact OMA.P_Erdos848_H3_R1_H1.not_dvd_25_ab ha25 hb₃_star (by simpa using hp2)
        have ha100 : a % 100 ∈ R3 := by
          have : a % 100 = 7 ∨ a % 100 = 43 := by omega
          rcases this with h | h <;> simp [R3, h]
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a % 100, ha100,
          Finset.mem_filter.mpr ⟨haI, by simp, p, hp, hp3, hp5, by omega, hp2⟩⟩)
    have hcovV : Vodd ⊆ V_sm13 ∪ V_tail := by
      intro a ha
      obtain ⟨haI, ⟨hstar, hodd⟩, hnsq⟩ := Finset.mem_filter.mp ha
      have hnsq' : ¬ Squarefree (a ^ 2 + 1) := by simpa [sq] using hnsq
      obtain ⟨q, hq, hqm4, hq13, hq2⟩ := OMA.P_Erdos848_H3_R1_H1.prime_sq_exists_sq_add_one hstar hnsq'
      by_cases hq2000 : q ≤ 2000
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨q,
          OMA.P_Erdos848_H3_R1_H1.mem_primes2000mod4.mpr ⟨hq13, hq2000, hq, hqm4⟩,
          Finset.mem_filter.mpr ⟨haI, hstar, hodd, hq2⟩⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨haI, q, hq, hqm4, by omega, hq2⟩)
    have hA1_hi := OMA.P_Erdos848_H3_R1_H1.card_ab_gt_sqrt_le hN_lo hN_hi hb₁_pos hb₁_le
    have hA3_hi := OMA.P_Erdos848_H3_R1_H1.card_ab_gt_sqrt_le hN_lo hN_hi hb₃_pos hb₃_le
    have hB1_sm : (B1_sm.card : ℝ) ≤ 6 * ((N : ℝ) / 100 * ((1622 / 10000 : ℝ) + 1 / 1000) + 167 + (Nat.sqrt N : ℝ)) := by
      have h1 : (B1_sm.card : ℝ) ≤ ∑ r ∈ R1, (((Finset.Icc 1 N).filter fun a => a % 100 = r % 100 ∧
          ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ 5 ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b₁ + 1).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      refine h1.trans ?_
      calc _ ≤ ∑ _r ∈ R1, ((N : ℝ) / 100 * ((1622 / 10000 : ℝ) + 1 / 1000) + 167 + (Nat.sqrt N : ℝ)) := by
            refine Finset.sum_le_sum fun r _ => ?_
            have h := OMA.P_Erdos848_H3_R1_H1.card_ab_le_sqrt_mod_le (N := N) (m := 100) (b := b₁) (r := r) (q_excl := 5)
              (by decide) hcop100 _ OMA.P_Erdos848_H3_R1_H1.sum_primes1000_ne5_le
            linarith
        _ = 6 * _ := by rw [Finset.sum_const, show R1.card = 6 by decide, nsmul_eq_mul]; norm_num
    have hB3_sm : (B3_sm.card : ℝ) ≤ 2 * ((N : ℝ) / 100 * ((1622 / 10000 : ℝ) + 1 / 1000) + 167 + (Nat.sqrt N : ℝ)) := by
      have h1 : (B3_sm.card : ℝ) ≤ ∑ r ∈ R3, (((Finset.Icc 1 N).filter fun a => a % 100 = r % 100 ∧
          ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ≠ 5 ∧ p ^ 2 ≤ N ∧ p ^ 2 ∣ a * b₃ + 1).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      refine h1.trans ?_
      calc _ ≤ ∑ _r ∈ R3, ((N : ℝ) / 100 * ((1622 / 10000 : ℝ) + 1 / 1000) + 167 + (Nat.sqrt N : ℝ)) := by
            refine Finset.sum_le_sum fun r _ => ?_
            have h := OMA.P_Erdos848_H3_R1_H1.card_ab_le_sqrt_mod_le (N := N) (m := 100) (b := b₃) (r := r) (q_excl := 5)
              (by decide) hcop100 _ OMA.P_Erdos848_H3_R1_H1.sum_primes1000_ne5_le
            linarith
        _ = 2 * _ := by rw [Finset.sum_const, show R3.card = 2 by decide, nsmul_eq_mul]; norm_num
    have hV_sm13 : (V_sm13.card : ℝ) ≤ 46 * ((N : ℝ) / 50 * (139 / 10000 : ℝ) + 150) := by
      let P13 := OMA.P_Erdos848_H3_R1_H1.primes2000mod4
      have hnat : V_sm13.card ≤ 46 * ∑ p ∈ P13, (N / (50 * p ^ 2) + 1) := by
        rw [Finset.mul_sum]
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p hp => ?_)
        obtain ⟨h13, _, hpr, _⟩ := OMA.P_Erdos848_H3_R1_H1.mem_primes2000mod4.mp hp
        exact OMA.P_Erdos848_H3_R1_H1.card_Icc_sq_add_one_isStar_odd_le hpr (by omega) (by omega)
      have hR1 := OMA.P_Erdos848_H3_R1_H1.sum_nat_div_add_one_le N 50 P13
      have hsum := OMA.P_Erdos848_H3_R1_H1.sum_primes2000_ge13_le
      have hP13_card : (P13.card : ℝ) ≤ 150 := by exact_mod_cast OMA.P_Erdos848_H3_R1_H1.card_primes2000mod4
      have hnatR : (V_sm13.card : ℝ) ≤ 46 * ((∑ p ∈ P13, (N / (50 * p ^ 2) + 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      simp only [Nat.cast_ofNat] at hR1
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    have hBad1_R : (Bad1.card : ℝ) ≤ (A1_hi.card : ℝ) + (B1_sm.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hcov1).trans (Finset.card_union_le _ _)
    have hBad3_R : (Bad3.card : ℝ) ≤ (A3_hi.card : ℝ) + (B3_sm.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hcov3).trans (Finset.card_union_le _ _)
    have hVodd_R : (Vodd.card : ℝ) ≤ (V_sm13.card : ℝ) + (V_tail.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hcovV).trans (Finset.card_union_le _ _)
    have hle_R : (Bad1.card : ℝ) + (Bad3.card : ℝ) + (Vodd.card : ℝ) ≤
        (((Finset.Icc 1 N).filter (fun a => a % 25 = 7)).card : ℝ) := by
      linarith
    exact_mod_cast hle_R
