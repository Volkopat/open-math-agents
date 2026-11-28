import OMAStatements.S_arxiv_2108_08753
import Mathlib

open OMA.S_arxiv_2108_08753

/-!
Disproof of the withdrawn conjecture of arXiv:2108.08753 that the parabola graph `Pi_p` on
`ZMod p × ZMod p` (two vertices `(x,y)`, `(z,w)` adjacent iff `(x + z)^2 = y + w`) has
independence number `p^(1+o(1))`, following M. Tait's construction (Theorem 2 of v2 of the paper):
for an odd prime `p` the grid `{1,...,floor(sqrt p / 8)} × (p/4, p/2)` of `F_p^2` is independent,
because `(x + z)^2 ≤ p/16 < p/2 < y + w` there, so `(x+z)^2` and `y+w` are unequal integers in
`[0, p)`.  Its size is `Theta(p^(3/2))`, hence for `eps = 1/8` and every `C` some prime `p`
carries an independent set bigger than `C * (p^2)^(1/2 + eps)`.
-/

private def gridMap (p : ℕ) : ℕ × ℕ → ZMod p × ZMod p :=
  fun r => (((r.1 + 1 : ℕ) : ZMod p), ((p / 4 + 1 + r.2 : ℕ) : ZMod p))

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2108_08753.main) := by
  rintro h
  obtain ⟨C, hC⟩ := h (1 / 8) (by norm_num)
  by_cases hCneg : C < 0
  · -- a negative constant is immediately refuted by the empty independent set at `p = 3`
    have hind : IsParabolaIndep 3 (∅ : Finset (ZMod 3 × ZMod 3)) := by
      intro u hu
      simp at hu
    have hkey := hC 3 (by norm_num) (by norm_num) ∅ hind
    simp only [Finset.card_empty, Nat.cast_zero] at hkey
    have hpos : (0 : ℝ) < ((3 : ℝ) * 3) ^ ((1 : ℝ) / 2 + 1 / 8) :=
      Real.rpow_pos_of_pos (by norm_num) _
    nlinarith
  · push Not at hCneg
    obtain ⟨N, hN⟩ := exists_nat_gt (max ((2048 * C) ^ 4) 16777216)
    have hNbig : 16777216 < N := by
      have h1 : (16777216 : ℝ) < (N : ℝ) := by
        have h2 : (16777216 : ℝ) ≤ max ((2048 * C) ^ 4) 16777216 := le_max_right _ _
        linarith
      exact_mod_cast h1
    obtain ⟨p, hpN, hpp⟩ := Nat.exists_infinite_primes (N + 2)
    have hp3 : 2 < p := by omega
    have hp0 : (0 : ℝ) < p := by
      have h1 : (0 : ℕ) < p := by omega
      exact_mod_cast h1
    have hp_large : (16777216 : ℝ) ≤ p := by
      have h1 : (16777216 : ℕ) ≤ p := by omega
      exact_mod_cast h1
    have hCsmall : (2048 * C) ^ 4 < (p : ℝ) := by
      have h1 : ((2048 * C) ^ 4) ≤ max ((2048 * C) ^ 4) 16777216 := le_max_left _ _
      have h2 : (N : ℝ) ≤ (p : ℝ) := by
        have h3 : N ≤ p := by omega
        exact_mod_cast h3
      linarith
    -- square roots of `p`
    have hsquares : ((p : ℝ)) ^ ((1 : ℝ) / 2) * ((p : ℝ) ^ ((1 : ℝ) / 2)) = (p : ℝ) := by
      rw [← Real.rpow_add hp0]
      norm_num
    -- integer bounds for the grid
    have hm_sq : Nat.sqrt p * Nat.sqrt p ≤ p := by
      simpa [Nat.pow_two] using Nat.sqrt_le' p
    have hp_sq : p < (Nat.sqrt p + 1) * (Nat.sqrt p + 1) := by
      simpa [Nat.pow_two] using Nat.lt_succ_sqrt' p
    have hp16 : 16 ≤ p := by omega
    have hKp : Nat.sqrt p / 8 < p := by
      have h1 : Nat.sqrt p / 8 ≤ Nat.sqrt p := Nat.div_le_self _ _
      have h2 : Nat.sqrt p < p := Nat.sqrt_lt_self (by omega)
      omega
    have hqp : p / 8 < p := by
      have h1 : p / 8 ≤ p := Nat.div_le_self _ _
      have h2 : p ≠ p / 8 := by
        intro hcon
        have : p ≤ 8 * (p / 8) + 8 := by omega
        omega
      omega
    have hbq : ∀ b : ℕ, b < p / 8 → p / 4 + 1 + b < p := by
      intro b hb
      have h1 : p ≤ 4 * (p / 4) + 4 := by omega
      omega
    set I : Finset (ZMod p × ZMod p) :=
      (Finset.range (Nat.sqrt p / 8) ×ˢ Finset.range (p / 8)).image (gridMap p) with hI
    -- the grid has the expected cardinality
    have hinj : Set.InjOn (gridMap p)
        ↑(Finset.range (Nat.sqrt p / 8) ×ˢ Finset.range (p / 8)) := by
      intro u hu v hv huv
      simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio] at hu hv
      obtain ⟨hu1, hu2⟩ := hu
      obtain ⟨hv1, hv2⟩ := hv
      have h1 : ((u.1 + 1 : ℕ) : ZMod p) = ((v.1 + 1 : ℕ) : ZMod p) := by
        have h := congrArg Prod.fst huv
        simpa [gridMap] using h
      have h2 : ((p / 4 + 1 + u.2 : ℕ) : ZMod p) = ((p / 4 + 1 + v.2 : ℕ) : ZMod p) := by
        have h := congrArg Prod.snd huv
        simpa [gridMap] using h
      have hu1p : u.1 + 1 < p := by omega
      have hv1p : v.1 + 1 < p := by omega
      have hu2p : p / 4 + 1 + u.2 < p := by
        exact hbq u.2 (by omega)
      have hv2p : p / 4 + 1 + v.2 < p := by
        exact hbq v.2 (by omega)
      have e1 : u.1 = v.1 := by
        have h := (ZMod.natCast_eq_natCast_iff' (u.1 + 1) (v.1 + 1) p).mp h1
        rw [Nat.mod_eq_of_lt hu1p, Nat.mod_eq_of_lt hv1p] at h
        omega
      have e2 : u.2 = v.2 := by
        have h :=
          (ZMod.natCast_eq_natCast_iff' (p / 4 + 1 + u.2) (p / 4 + 1 + v.2) p).mp h2
        rw [Nat.mod_eq_of_lt hu2p, Nat.mod_eq_of_lt hv2p] at h
        omega
      exact Prod.ext e1 e2
    have hIcard : I.card = (Nat.sqrt p / 8) * (p / 8) := by
      rw [hI, Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_range,
        Finset.card_range]
    -- the grid is independent: `(x + z)^2 ≤ p/16 < p/2 < y + w`, and both sides are `< p`
    have hindep : IsParabolaIndep p I := by
      rintro u hu v hv hAdj
      obtain ⟨-, heq⟩ := hAdj
      rw [hI] at hu hv
      obtain ⟨⟨a, b⟩, hab, hua⟩ := Finset.mem_image.mp hu
      obtain ⟨⟨a', b'⟩, hab', hva⟩ := Finset.mem_image.mp hv
      simp only [Finset.mem_product, Finset.mem_range] at hab hab'
      obtain ⟨haK, hbq'⟩ := hab
      obtain ⟨haK', hbq''⟩ := hab'
      rw [← hua, ← hva] at heq
      simp only [gridMap] at heq
      have key : ((((a + 1) + (a' + 1)) ^ 2 : ℕ) : ZMod p) =
          (((p / 4 + 1 + b) + (p / 4 + 1 + b') : ℕ) : ZMod p) := by
        push_cast
        simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using heq
      -- the two natural numbers are both `< p` and are unequal
      have hstep2 : 16 * ((Nat.sqrt p / 4) ^ 2) ≤ Nat.sqrt p * Nat.sqrt p := by
        have h4 : 4 * (Nat.sqrt p / 4) ≤ Nat.sqrt p := Nat.mul_div_le _ _
        have h5 := Nat.mul_le_mul h4 h4
        calc 16 * ((Nat.sqrt p / 4) ^ 2) = (4 * (Nat.sqrt p / 4)) * (4 * (Nat.sqrt p / 4)) := by
              ring
          _ ≤ Nat.sqrt p * Nat.sqrt p := h5
      have h16 : 16 * (((a + 1) + (a' + 1)) ^ 2) ≤ p := by
        have haa : (a + 1) + (a' + 1) ≤ Nat.sqrt p / 4 := by omega
        have hs1 : ((a + 1) + (a' + 1)) ^ 2 ≤ (Nat.sqrt p / 4) ^ 2 :=
          Nat.pow_le_pow_left haa 2
        have hs2 : 16 * (((a + 1) + (a' + 1)) ^ 2) ≤ 16 * ((Nat.sqrt p / 4) ^ 2) :=
          Nat.mul_le_mul_left 16 hs1
        omega
      have h2t : p ≤ 2 * ((p / 4 + 1 + b) + (p / 4 + 1 + b')) := by omega
      have hs_lt : ((a + 1) + (a' + 1)) ^ 2 < p := by omega
      have hst : ((a + 1) + (a' + 1)) ^ 2 < (p / 4 + 1 + b) + (p / 4 + 1 + b') := by omega
      have ht_lt : (p / 4 + 1 + b) + (p / 4 + 1 + b') < p := by
        have h1 : p / 4 + 1 + b ≤ p / 4 + p / 8 := by omega
        have h2 : p / 4 + 1 + b' ≤ p / 4 + p / 8 := by omega
        omega
      have hmod := (ZMod.natCast_eq_natCast_iff' _ _ p).mp key
      rw [Nat.mod_eq_of_lt hs_lt, Nat.mod_eq_of_lt ht_lt] at hmod
      omega
    -- size, in the reals
    have hq_lb : (p : ℝ) / 32 ≤ ((p / 8 : ℕ) : ℝ) := by
      have h1 : (p : ℝ) ≤ 8 * ((p / 8 : ℕ) : ℝ) + 8 := by
        have h2 : p ≤ 8 * (p / 8) + 8 := by omega
        exact_mod_cast h2
      linarith
    have hK_lb : ((p : ℝ) ^ ((1 : ℝ) / 2)) / 32 ≤ ((Nat.sqrt p / 8 : ℕ) : ℝ) := by
      have hm_sq' : ((Nat.sqrt p : ℝ)) * (Nat.sqrt p : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast hm_sq
      have hp_sq' : (p : ℝ) < ((Nat.sqrt p : ℝ) + 1) * ((Nat.sqrt p : ℝ) + 1) := by
        exact_mod_cast hp_sq
      have hm0 : (0 : ℝ) ≤ (Nat.sqrt p : ℝ) := by positivity
      have hS_le : ((p : ℝ)) ^ ((1 : ℝ) / 2) ≤ (p : ℝ) / 2 := by
        nlinarith [hsquares, hp_large]
      have hm_ge : ((p : ℝ) ^ ((1 : ℝ) / 2)) / 2 ≤ (Nat.sqrt p : ℝ) := by
        nlinarith [hsquares, hm_sq', hp_sq', hm0, hp_large, hS_le]
      have h1 : (Nat.sqrt p : ℝ) ≤ 8 * ((Nat.sqrt p / 8 : ℕ) : ℝ) + 8 := by
        have h2 : Nat.sqrt p ≤ 8 * (Nat.sqrt p / 8) + 8 := by omega
        exact_mod_cast h2
      have hS32 : (32 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := by
        have hbase : (0 : ℝ) ≤ (32 : ℝ) ^ 2 := by positivity
        have hmono : ((32 : ℝ) ^ 2) ^ ((1 : ℝ) / 2) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow hbase (by norm_num; linarith) (by norm_num)
        have hval : ((32 : ℝ) ^ 2) ^ ((1 : ℝ) / 2) = 32 := by
          rw [show ((32 : ℝ) ^ 2) = (32 : ℝ) ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 32)]
          norm_num
        linarith
      linarith
    have hcard_lb : ((p : ℝ) ^ ((3 : ℝ) / 2)) / 1024 ≤ (I.card : ℝ) := by
      rw [hIcard]
      push_cast
      have hp32 : (p : ℝ) ^ ((3 : ℝ) / 2) = (p : ℝ) ^ ((1 : ℝ) / 2) * (p : ℝ) := by
        rw [show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num, Real.rpow_add hp0,
          Real.rpow_one]
      rw [hp32]
      have hS0 : (0 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hp0) _
      nlinarith [hK_lb, hq_lb, hS0]
    -- comparison with the claimed bound
    have hT : 2048 * C < (p : ℝ) ^ ((1 : ℝ) / 4) := by
      have h512 : (0 : ℝ) ≤ 2048 * C := by linarith
      have hbase : (0 : ℝ) ≤ (2048 * C) ^ 4 := by positivity
      have hrpow := Real.rpow_lt_rpow hbase hCsmall (by norm_num : (0 : ℝ) < 1 / 4)
      have hleft : ((2048 * C) ^ 4 : ℝ) ^ ((1 : ℝ) / 4) = 2048 * C := by
        rw [show ((2048 * C) ^ 4 : ℝ) = (2048 * C) ^ ((4 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
        rw [← Real.rpow_mul h512]
        norm_num
      rwa [hleft] at hrpow
    have hsplit : (p : ℝ) ^ ((3 : ℝ) / 2) =
        (p : ℝ) ^ ((5 : ℝ) / 4) * (p : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hp0]
      norm_num
    have hP : (0 : ℝ) < (p : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_pos_of_pos hp0 _
    have hmain : C * (p : ℝ) ^ ((5 : ℝ) / 4) < (p : ℝ) ^ ((3 : ℝ) / 2) / 1024 := by
      have hP32 : (0 : ℝ) < (p : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
      have step : (2048 * C) * (p : ℝ) ^ ((5 : ℝ) / 4) < (p : ℝ) ^ ((1 : ℝ) / 4) *
          (p : ℝ) ^ ((5 : ℝ) / 4) := mul_lt_mul_of_pos_right hT hP
      have hcomm : (p : ℝ) ^ ((1 : ℝ) / 4) * (p : ℝ) ^ ((5 : ℝ) / 4) =
          (p : ℝ) ^ ((3 : ℝ) / 2) := by
        rw [hsplit]
        ring
      linarith [step, hcomm]
    have hconv : ((p : ℝ) * (p : ℝ)) ^ ((1 : ℝ) / 2 + 1 / 8) = (p : ℝ) ^ ((5 : ℝ) / 4) := by
      have hp2' : ((p : ℝ) * (p : ℝ)) = (p : ℝ) ^ ((2 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; ring
      rw [hp2', ← Real.rpow_mul (le_of_lt hp0)]
      norm_num
    have hcontra := hC p hpp hp3 I hindep
    rw [hconv] at hcontra
    linarith
