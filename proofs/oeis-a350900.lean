import OMAStatements.S_oeis_a350900
import Mathlib

/-!
Werner Schulte posed the identities in OEIS A350900 (https://oeis.org/A350900).
The Lean statement is by @sturdy4days in
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8272.
We count the fibers of gcd on a full residue system and express the result
as an iterated Dirichlet convolution.
-/

open Finset ArithmeticFunction OMA.S_oeis_a350900
open scoped ArithmeticFunction.zeta

namespace OMA.A350900Proof

private theorem sum_Icc_eq_range (n : ℕ) (F : ℕ → ℂ) (h : F n = F 0) :
    ∑ i ∈ Icc 1 n, F i = ∑ i ∈ range n, F i := by
  have hi : insert 0 (Icc 1 n) = range (n + 1) := by
    ext i
    simp only [mem_insert, mem_Icc, mem_range]
    omega
  have hr : insert n (range n) = range (n + 1) := by
    ext i
    simp only [mem_insert, mem_range]
    omega
  have he := congrArg (fun s : Finset ℕ => ∑ i ∈ s, F i) (hi.trans hr.symm)
  have hzero : 0 ∉ Icc 1 n := by simp
  have hn : n ∉ range n := by simp
  rw [sum_insert hzero, sum_insert hn, h] at he
  exact add_left_cancel he

private theorem sum_gcd_fibers (n : ℕ) (hn : n ≠ 0) (F : ℕ → ℂ) :
    ∑ j ∈ range n, F (n.gcd j) =
      ∑ d ∈ n.divisors, ((n / d).totient : ℂ) * F d := by
  have hmap (j : ℕ) (_ : j ∈ range n) : n.gcd j ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n j, hn⟩
  rw [← sum_fiberwise_of_maps_to' hmap F]
  refine sum_congr rfl fun d hd => ?_
  rw [sum_const, nsmul_eq_mul, Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]

private theorem sum_gcd_blocks (g q : ℕ) (F : ℕ → ℂ) :
    ∑ k ∈ range (q * g), F (g.gcd k) = (q : ℂ) * ∑ k ∈ range g, F (g.gcd k) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, sum_range_add, ih, Nat.cast_succ, add_mul, one_mul]
    congr 1
    exact sum_congr rfl fun k _ => by simp [Nat.add_comm (q * g) k]

private def weighted (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun d => f d * (d.totient : ℂ), by simp⟩

private theorem convolution_apply (F G : ArithmeticFunction ℂ) (n : ℕ) :
    (F * G) n = ∑ d ∈ n.divisors, F d * G (n / d) := by
  rw [ArithmeticFunction.mul_apply]
  exact Nat.sum_divisorsAntidiagonal (fun d e => F d * G e)

private theorem inner_sum (f : ℕ → ℂ) (n g : ℕ) (hg : 0 < g) (hgn : g ∣ n) :
    ∑ k ∈ Icc 1 n, f (g / g.gcd k) = ((n / g : ℕ) : ℂ) * (weighted f * ζ) g := by
  rw [sum_Icc_eq_range n (fun k => f (g / g.gcd k)) (by simp [Nat.gcd_eq_left hgn])]
  have hb := sum_gcd_blocks g (n / g) (fun d => f (g / d))
  rw [Nat.div_mul_cancel hgn] at hb
  rw [hb, sum_gcd_fibers g hg.ne' (fun d => f (g / d)),
    Nat.sum_div_divisors g (fun d => (d.totient : ℂ) * f d), coe_mul_zeta_apply]
  congr 1
  exact sum_congr rfl fun d _ => by simp [weighted, mul_comm]

private theorem row_convolution (f : ℕ → ℂ) (n : ℕ) :
    weightedRowSum f n = (weighted f * (ζ * weighted (fun d => (d : ℂ)))) n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [weightedRowSum]
  let F (g : ℕ) := ∑ k ∈ Icc 1 n, f (g / g.gcd k)
  calc
    weightedRowSum f n = ∑ i ∈ Icc 1 n, F (n.gcd i) := by
      unfold weightedRowSum F
      refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
      have hgcd : (i.gcd k).gcd n = (n.gcd i).gcd k := by
        rw [Nat.gcd_assoc, Nat.gcd_comm k n, ← Nat.gcd_assoc, Nat.gcd_comm i n]
      rw [hgcd, Nat.gcd_comm i n]
    _ = ∑ i ∈ range n, F (n.gcd i) :=
      sum_Icc_eq_range n (fun i => F (n.gcd i)) (by simp)
    _ = ∑ g ∈ n.divisors, ((n / g).totient : ℂ) * F g := sum_gcd_fibers n hn.ne' F
    _ = ((weighted f * ζ) * weighted (fun d => (d : ℂ))) n := by
      rw [convolution_apply]
      refine sum_congr rfl fun g hg => ?_
      dsimp only [F]
      rw [inner_sum f n g (Nat.pos_of_mem_divisors hg) (Nat.dvd_of_mem_divisors hg)]
      change ((n / g).totient : ℂ) * (((n / g : ℕ) : ℂ) * (weighted f * ζ) g) =
        (weighted f * ζ) g * (((n / g : ℕ) : ℂ) * ((n / g).totient : ℂ))
      ring
    _ = (weighted f * (ζ * weighted (fun d => (d : ℂ)))) n := by rw [mul_assoc]

private theorem order_sum_convolution (n : ℕ) :
    (ζ * weighted (fun d => (d : ℂ))) n = (orderSum n : ℂ) := by
  rw [coe_zeta_mul_apply]
  simp [orderSum, weighted]

private theorem first_identity (f : ℕ → ℂ) (n : ℕ) :
    weightedRowSum f n =
      ∑ d ∈ n.divisors, f d * (d.totient : ℂ) * (orderSum (n / d) : ℂ) := by
  rw [row_convolution, convolution_apply]
  exact sum_congr rfl fun d _ => by rw [order_sum_convolution]; rfl

private theorem weighted_multiplicative (f : ℕ → ℂ)
    (hf : OMA.S_oeis_a350900.IsMultiplicative f) :
    (weighted f).IsMultiplicative := by
  refine ⟨by simp [weighted, hf.1], ?_⟩
  intro m n hcop
  change f (m * n) * ((m * n).totient : ℂ) =
    (f m * (m.totient : ℂ)) * (f n * (n.totient : ℂ))
  rw [hf.2 m n hcop, Nat.totient_mul hcop, Nat.cast_mul]
  ring

private theorem totient_square (d : ℕ) (hd : 0 < d) :
    (d ^ 2).totient = d * d.totient := by
  have h := Nat.totient_gcd_mul_totient_mul d d
  rw [Nat.gcd_self, ← pow_two] at h
  exact Nat.mul_left_cancel (Nat.totient_pos.mpr hd) (h.trans (by ring))

end OMA.A350900Proof

open OMA.A350900Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a350900.main := by
  refine ⟨fun f n _ => first_identity f n, ?_, ?_⟩
  · intro f hf
    have hid : OMA.S_oeis_a350900.IsMultiplicative (fun d => (d : ℂ)) :=
      ⟨Nat.cast_one, fun a b _ => Nat.cast_mul a b⟩
    have hζ : (↑ζ : ArithmeticFunction ℂ).IsMultiplicative :=
      isMultiplicative_zeta.natCast
    have hm := (weighted_multiplicative f hf).mul
      (hζ.mul (weighted_multiplicative _ hid))
    refine ⟨?_, ?_⟩
    · rw [row_convolution]
      exact hm.1
    · intro a b hab
      simp only [row_convolution]
      exact hm.2 hab
  · intro n _
    rw [first_identity]
    refine sum_congr rfl fun d hd => ?_
    rw [totient_square d (Nat.pos_of_mem_divisors hd), Nat.cast_mul]
