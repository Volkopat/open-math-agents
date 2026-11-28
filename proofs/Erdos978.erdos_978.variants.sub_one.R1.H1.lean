import OMAReductions.R_Erdos978_erdos_978_variants_sub_one_R1
import Mathlib

-- Step Erdos978.erdos_978.variants.sub_one.R1.H1: hypothesis H1 of reduction Erdos978.erdos_978.variants.sub_one.R1
-- Credit: @koolkao

/-!
# Small-prime sieve for `(k-1)`-th-power-free values on `(N, 2N]`

Original proof (Lane C, claude-code for koolkao). Fix `w` large. The residues `n mod ∏_{p ≤ w} p^(k-1)`
avoiding every `p^(k-1) ∣ f(n)` form a set of density at least `c > 0` (each local factor is positive by
the hypothesis; for `p` beyond the bad primes the local density is `≥ 1 - k/p²` because roots modulo
`p^(k-1)` reduce injectively to roots modulo `p`, by the Bezout identity `f u + f' v = D`). Primes
`p ∈ (w, N]` remove at most `k (N/p² + 1)` inputs each, in total `≤ 2kN/w + k π(N)`. Hence a proportion
`≥ c/4` of `(N, 2N]` survives for all large `N`.

The file also carries (unused here) the development of my #9300, whose helper lemmas it reuses.
-/

/-! Part 1: the algebraic bridge. For an irreducible `f ∈ ℤ[X]` we build the number field
`K = ℚ[X]/(f)`, the algebraic integer `θ = a·root` (`a` the leading coefficient), and for a prime
`p ∤ a·exponent θ` and a root `c` of `f` mod `p` the ideal `J p c = (p, θ - a c)` of norm `p`
(Kummer–Dedekind, Mathlib). Distinct pairs give coprime ideals. -/

noncomputable section
open Polynomial NumberField Ideal

namespace LaneC976

section setup

variable (f : ℤ[X])

/-- `f` over `ℚ`. -/
abbrev fQ : ℚ[X] := f.map (Int.castRingHom ℚ)

variable {f} [hfi : Fact (Irreducible (fQ f))]

end setup

end LaneC976

end

/-! Part 2: a Chebyshev–Mertens upper bound for families of pairwise coprime ideals of a
number field, from the ideal-counting asymptotic `#{I ≠ 0 : N I ≤ s} ~ κ s` (Mathlib). -/

noncomputable section
open Filter Topology Ideal NumberField Finset
open scoped nonZeroDivisors

namespace LaneC976

variable {K : Type*} [Field K] [NumberField K]

end LaneC976

end

/-! Part 3: local counting. Bezout `f u + f' v = D`, clustering of the solutions of
`p^j ∣ f(k)`, and the bound on `#{k ≤ n : p^j ∣ f(k)}`. -/

noncomputable section
open Polynomial Finset

namespace LaneC976

/-- Bezout identity with a nonzero integer, from the resultant of `f` and `f'`. -/
theorem exists_bezout (f : ℤ[X]) (hf : Irreducible (f.map (Int.castRingHom ℚ)))
    (hd : 1 ≤ f.natDegree) :
    ∃ u v : ℤ[X], ∃ D : ℤ, D ≠ 0 ∧ f * u + derivative f * v = C D := by
  obtain ⟨u, v, -, -, h⟩ := exists_mul_add_mul_eq_C_resultant f (derivative f) le_rfl le_rfl
    (Or.inl (by omega))
  refine ⟨u, v, _, ?_, h⟩
  have hinj := RingHom.injective_int (Int.castRingHom ℚ)
  intro h0
  have hsep : (f.map (Int.castRingHom ℚ)).Separable := hf.separable
  have hcop : IsCoprime (f.map (Int.castRingHom ℚ)) (derivative (f.map (Int.castRingHom ℚ))) :=
    hsep
  have h1 := resultant_ne_zero _ _ hcop
  rw [derivative_map] at h1
  have e1 : (f.map (Int.castRingHom ℚ)).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective hinj f
  have e2 : ((derivative f).map (Int.castRingHom ℚ)).natDegree = (derivative f).natDegree :=
    natDegree_map_eq_of_injective hinj _
  apply h1
  have := resultant_map_map f (derivative f) f.natDegree (derivative f).natDegree
    (Int.castRingHom ℚ)
  rw [h0, map_zero] at this
  rw [e1, e2]; exact this

/-- Clustering of solutions of `p^j ∣ f(x)` (Hensel-type, via the Bezout identity). -/
theorem cluster {f u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D)
    {p : ℕ} (hp : p.Prime) {δ j : ℕ} (hδ : ¬ (p : ℤ) ^ (δ + 1) ∣ D) (hj : δ + 1 ≤ j)
    {x y : ℤ} (hx : (p : ℤ) ^ j ∣ f.eval x) (hy : (p : ℤ) ^ j ∣ f.eval y)
    (hxy : (p : ℤ) ^ (δ + 1) ∣ y - x) : (p : ℤ) ^ (j - δ) ∣ y - x := by
  have hD : f.eval x * u.eval x + (derivative f).eval x * v.eval x = D := by
    have := congrArg (eval x) hB; simpa using this
  have hpd : ¬ (p : ℤ) ^ (δ + 1) ∣ (derivative f).eval x := by
    intro h; apply hδ; rw [← hD]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow _ hj) hx) _)
      (dvd_mul_of_dvd_left h _)
  obtain ⟨w, hw⟩ := binomExpansion f x (y - x)
  set U := (derivative f).eval x + w * (y - x) with hUdef
  have hfy : f.eval y - f.eval x = (y - x) * U := by
    have : x + (y - x) = y := by ring
    rw [this] at hw; rw [hw, hUdef]; ring
  have hU : ¬ (p : ℤ) ^ (δ + 1) ∣ U := by
    intro h; apply hpd
    have : (derivative f).eval x = U - w * (y - x) := by rw [hUdef]; ring
    rw [this]; exact dvd_sub h (dvd_mul_of_dvd_right hxy _)
  have hdiv : (p : ℤ) ^ j ∣ (y - x) * U := hfy ▸ dvd_sub hy hx
  by_cases hyx : y - x = 0
  · rw [hyx]; exact dvd_zero _
  have hU0 : U ≠ 0 := by rintro h; exact hU (h ▸ dvd_zero _)
  haveI := Fact.mk hp
  have h1 := (padicValInt_dvd_iff (p := p) j ((y - x) * U)).mp hdiv
  rcases h1 with h1 | h1
  · exact absurd h1 (mul_ne_zero hyx hU0)
  rw [padicValInt.mul hyx hU0] at h1
  have h2 : padicValInt p U ≤ δ := by
    by_contra h2
    exact hU ((padicValInt_dvd_iff (p := p) (δ + 1) U).mpr (Or.inr (by omega)))
  exact (padicValInt_dvd_iff (p := p) (j - δ) (y - x)).mpr (Or.inr (by omega))

end LaneC976

end

/-! Part 4: elementary facts about `f` (no integer roots, size of `f(k)`), and `log n!`. -/

noncomputable section
open Polynomial Finset Real Filter

namespace LaneC976

end LaneC976

end

/-! Part 5: `∑ log |f(k)|` as a sum over primes, and the bound for each prime. -/

noncomputable section
open Polynomial Finset

namespace LaneC976

end LaneC976

end

/-! Part 6: the concrete Mertens bound for `ρ(p) = #{c < p : p ∣ f(c)}`, and small lemmas. -/

noncomputable section
open Polynomial Finset Filter NumberField Ideal

namespace LaneC976

/-- The number of roots of `f` modulo `p` in `[0, p)`. -/
def rho (f : ℤ[X]) (p : ℕ) : ℕ := #{c ∈ range p | (p : ℤ) ∣ f.eval ((c : ℕ) : ℤ)}

theorem rho_le {f : ℤ[X]} {p : ℕ} (hp : p.Prime) (hpa : ¬ (p : ℤ) ∣ f.leadingCoeff) :
    rho f p ≤ f.natDegree := by
  classical
  haveI := Fact.mk hp
  set g := f.map (Int.castRingHom (ZMod p)) with hgdef
  have hlc : (Int.castRingHom (ZMod p)) f.leadingCoeff ≠ 0 := by
    rwa [Ne, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hg : g.natDegree = f.natDegree := natDegree_map_of_leadingCoeff_ne_zero _ hlc
  have hg0 : g ≠ 0 := by
    intro h
    have : g.leadingCoeff = 0 := by rw [h, leadingCoeff_zero]
    rw [hgdef, leadingCoeff_map_of_leadingCoeff_ne_zero _ hlc] at this
    exact hlc this
  calc rho f p ≤ #(g.roots.toFinset) := by
        refine card_le_card_of_injOn (fun c : ℕ ↦ (c : ZMod p)) (fun c hc ↦ ?_) (fun c hc c' hc' e ↦ ?_)
        · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hc
          rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hg0, IsRoot]
          simp only
          rw [show ((c : ℕ) : ZMod p) = ((c : ℤ) : ZMod p) by simp, hgdef, eval_intCast_map,
            eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact hc.2
        · rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hc hc'
          simp only at e
          rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hc.1, Nat.mod_eq_of_lt hc'.1] at e
          exact e
    _ ≤ Multiset.card g.roots := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := card_roots' g
    _ = f.natDegree := hg

theorem dvd_eval_mod {f : ℤ[X]} {p k : ℕ} (h : (p : ℤ) ∣ f.eval (k : ℤ)) :
    (p : ℤ) ∣ f.eval ((k % p : ℕ) : ℤ) := by
  have h1 := sub_dvd_eval_sub ((k % p : ℕ) : ℤ) (k : ℤ) f
  have h2 : (p : ℤ) ∣ ((k % p : ℕ) : ℤ) - k := by
    rw [Int.natCast_mod]
    have := (Int.mod_modEq (k : ℤ) p).dvd
    rw [← dvd_neg, neg_sub]; exact this
  have h3 := dvd_trans h2 h1
  have := dvd_add h3 h
  simpa using this

end LaneC976

end

/-! Part 7: the Mertens bound `∑_{p ≤ n good} ρ(p) log p / p ≤ (3/2) log n + C`. -/

noncomputable section
open Polynomial Finset Filter NumberField Ideal

namespace LaneC976

end LaneC976

end

/-! Part 8: assembly. -/

noncomputable section
open Polynomial Finset Filter NumberField Ideal

namespace LaneC976

end LaneC976

end

/-! Part 9: per-prime bounds in the form used by the assembly. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC976

end LaneC976

end

/-! Stepanov part 1: the derivative polynomials `Hp` with `g^u (g^N)^{(u)} = g^N Hp u`,
their degree bound, and `X^(b q)` behaving as a constant for derivatives in characteristic `q`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

variable {F : Type*} [Field F]

/-- `Hp g c u` with `c = (N : F)`: `g^u · (g^N)^{(u)} = g^N · Hp g c u`. -/
def Hp (g : F[X]) (c : F) : ℕ → F[X]
  | 0 => 1
  | u + 1 => C (c - u) * derivative g * Hp g c u + g * derivative (Hp g c u)

end LaneC978

end

/-! Stepanov part 2: the Leibniz identity for `g^m (A g^{js} X^{bq})^{(m)}` in characteristic `q`
and its evaluation at points with `g(r)^s = 1`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

variable {q : ℕ} [hq : Fact q.Prime]


end LaneC978

end

/-! Stepanov part 3: linear algebra. The coefficients of the `Q_m` are linear in the
coefficients of the `A_i`; more unknowns than equations gives a nonzero solution. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

variable {q : ℕ} [hq : Fact q.Prime]


variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

end LaneC978

end

/-! Stepanov part 4: the bound `#{r : g(r)^s = 1} ≤ (1 - 1/(4ℓ)) q` for `ℓ s = q - 1`,
`deg g = k` coprime to `ℓ`, and `q` large. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

variable {q : ℕ} [hq : Fact q.Prime]


end LaneC978

end

/-! Stepanov part 5: the bound itself. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

variable {q : ℕ} [hq : Fact q.Prime]


end LaneC978

end

/-! Stepanov part 6: assembly of the bound `4ℓ #{r : g(r)^s = 1} ≤ (4ℓ - 1) q`. -/

noncomputable section
open Polynomial Finset
open scoped Function

namespace LaneC978

variable {q : ℕ} [hq : Fact q.Prime]


end LaneC978

end

/-! Lemma 3, part a: elementary facts on `ρ(m) = #{r < m : m ∣ f(r)}` — reduction of roots,
submultiplicativity over coprime moduli, uniform bounds at bad prime powers, smooth moduli. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

theorem dvd_eval_mod {f : ℤ[X]} {m d r : ℕ} (hd : d ∣ m) (hr : (m : ℤ) ∣ f.eval (r : ℤ)) :
    (d : ℤ) ∣ f.eval ((r % d : ℕ) : ℤ) := by
  have h1 := sub_dvd_eval_sub ((r % d : ℕ) : ℤ) (r : ℤ) f
  have h2 : (d : ℤ) ∣ ((r % d : ℕ) : ℤ) - r := by
    have := (Nat.mod_modEq r d)
    have h3 := (Nat.modEq_iff_dvd.mp this)
    rw [← dvd_neg, neg_sub]; exact h3
  have h4 : (d : ℤ) ∣ f.eval (r : ℤ) := (Int.natCast_dvd_natCast.mpr hd).trans hr
  have := dvd_add (h2.trans h1) h4
  simpa using this

end LaneC978

end

/-! Lemma 3, part b: for a modulus `m` all of whose prime factors are good, the roots of `f`
modulo `m` inject into the ideals of norm `m` of the ring of integers. -/

noncomputable section
open Polynomial Finset NumberField Ideal

namespace LaneC978

open LaneC976

variable {K : Type*} [Field K] [NumberField K]

end LaneC978

end

/-! Lemma 3, part c: `∑_{m ≤ x} ρ(m) ≤ C x` for irreducible `f`. -/

noncomputable section
open Polynomial Finset NumberField Ideal

namespace LaneC978

open LaneC976

variable {K : Type*} [Field K] [NumberField K]

end LaneC978

end

/-! Lemma 3, part d: `∑_{m ≤ x} ρ(m) ≤ C x` for `f` irreducible over `ℚ`. -/

noncomputable section
open Polynomial Finset NumberField Ideal

namespace LaneC978

open LaneC976

end LaneC978

end

/-! Counting integers in residue classes: `#{n < N : n mod W ∈ T} ≤ #T (N/W + 1)`, and the
Chinese remainder combination of a root condition mod `m` with conditions mod primes `q`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

end LaneC978

end

/-! The local power-residue bound: for `q ≡ 1 (mod ℓ)` large and `q ∤ m`, at most a fraction
`1 - 1/(4ℓ)` of the residues `r mod q` have `f(r)/m` an `ℓ`-th power residue. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

end LaneC978

end

/-! Few `n < N` have many prime factors from a fixed finite set `Q` of primes dividing `f(n)`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

end LaneC978

end

/-! The bound on one dyadic level `b^z ≤ N/m < b^(z+1)` of cofactors `m`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

end LaneC978

end

/-! The count of one level, after removing the inputs with many small prime divisors. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

end LaneC978

end

/-! Summing the level bound over the cofactors of one level. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

end LaneC978

end

/-! Primes `≡ 1 (mod ℓ)` are not too sparse: for every `A`, eventually more than `A log x` primes
`p ≡ 1 (mod ℓ)` divide `∏_{k ≤ x} Φ_ℓ(k)`. Elementary, via the Nagell-type valuation budget. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

end LaneC978

end

/-! The budget argument for `Φ_ℓ`. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

end LaneC978

end

/-! For every `c`, eventually `c · log₂ z ≤ #{q ≤ z prime : q > q0, q ≡ 1 (mod ℓ)}`. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

end LaneC978

end

/-! The case `ℓ = 2`: odd primes, from Chebyshev's lower bound. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

end LaneC978

end

/-! The covering of the exceptional set: small `n`, cofactors of low level (few large primes),
inputs with many small prime factors, and the sieved sets. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

open Classical in
/-- The exceptional set below `N`. -/
def Exc (f : ℤ[X]) (N : ℕ) : Finset ℕ :=
  (range N).filter fun n => ∃ p, p.Prime ∧ N < p ∧ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval ((n : ℕ) : ℤ)

end LaneC978

end

/-! The bound for one level `z` in terms of `1/z²`. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

end LaneC978

end

/-! The large-prime estimate: for every `ε > 0`, eventually `#Exc(N) ≤ ε N`. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

theorem sum_inv_sq_le (a : ℕ) (ha : 1 ≤ a) :
    ∀ Z : ℕ, a ≤ Z → ∑ z ∈ Icc a Z, (1 : ℝ) / (z : ℝ) ^ 2 ≤ 2 / a - 1 / Z := by
  intro Z hZ
  induction Z, hZ using Nat.le_induction with
  | base =>
    rw [Icc_self, sum_singleton]
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  | succ Z hZ ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hZ1 : (1 : ℝ) ≤ Z := by exact_mod_cast (le_trans ha hZ)
    have h : (1 : ℝ) / ((Z + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / Z - 1 / (Z + 1 : ℕ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

theorem sum_inv_sq_le' (a Z : ℕ) (ha : 1 ≤ a) :
    ∑ z ∈ Icc a Z, (1 : ℝ) / (z : ℝ) ^ 2 ≤ 2 / a := by
  by_cases h : a ≤ Z
  · have := sum_inv_sq_le a ha Z h
    have : (0 : ℝ) ≤ 1 / Z := by positivity
    linarith
  · rw [Icc_eq_empty (by omega), sum_empty]; positivity

/-- `k π(T N) ≤ (ε/4) N` eventually. -/
theorem pi_small (k T : ℕ) (hT : 1 ≤ T) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (k : ℝ) * Nat.primeCounting (T * N) ≤ ε / 4 * N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  filter_upwards [hlog.eventually_ge_atTop (16 * k * Real.log 4 * T / ε + 1),
    hsq.eventually_ge_atTop (8 * k * Real.sqrt T / ε + 1), eventually_ge_atTop 2] with N h1 h2 hN2
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  set x : ℝ := (T : ℝ) * N with hx
  have hx1 : 1 < x := by rw [hx]; nlinarith
  have hpi := Chebyshev.pi_le_log4_mul_div hx1
  rw [show ⌊x⌋₊ = T * N by rw [hx]; exact_mod_cast Nat.floor_natCast (T * N)] at hpi
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlx : Real.log N / 2 ≤ Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt (by linarith), hx, Real.log_mul (by positivity) (by positivity)]
    have := Real.log_nonneg hTr; linarith
  have hlxpos : 0 < Real.log (Real.sqrt x) := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hsqx : Real.sqrt x = Real.sqrt T * Real.sqrt N := by
    rw [hx, Real.sqrt_mul (by positivity)]
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by positivity)
  have hsqN0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have t1 : (k : ℝ) * (Real.log 4 * x / Real.log (Real.sqrt x)) ≤ ε / 8 * N := by
    rw [mul_div_assoc', div_le_iff₀ hlxpos]
    have : 16 * k * Real.log 4 * T / ε ≤ Real.log N := by linarith
    rw [div_le_iff₀ hε] at this
    rw [hx]
    have hNn : (0 : ℝ) ≤ N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlx (show (0 : ℝ) ≤ ε / 8 * N by positivity)]
  have t2 : (k : ℝ) * Real.sqrt x ≤ ε / 8 * N := by
    rw [hsqx]
    have : 8 * k * Real.sqrt T / ε ≤ Real.sqrt N := by linarith
    rw [div_le_iff₀ hε] at this
    calc (k : ℝ) * (Real.sqrt T * Real.sqrt N) = (k * Real.sqrt T) * Real.sqrt N := by ring
      _ ≤ (ε / 8 * Real.sqrt N) * Real.sqrt N :=
          mul_le_mul_of_nonneg_right (by linarith) hsqN0.le
      _ = ε / 8 * N := by rw [mul_assoc, hsqN]
  calc (k : ℝ) * Nat.primeCounting (T * N) ≤ k * (Real.log 4 * x / Real.log (Real.sqrt x) +
        Real.sqrt x) := mul_le_mul_of_nonneg_left hpi hk0
    _ = k * (Real.log 4 * x / Real.log (Real.sqrt x)) + k * Real.sqrt x := by ring
    _ ≤ ε / 8 * N + ε / 8 * N := add_le_add t1 t2
    _ = ε / 4 * N := by ring

end LaneC978

end

/-! The final assembly: the large-prime estimate of Hooley for `(k-1)`-th powers. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

end LaneC978

end

/-! The step `Erdos978.erdos_978.parts.i.R1.H2`, in the reduction's own form. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

end LaneC978

end

/-! Tools for the small-prime sieve: CRT lower bound, counts in `(N, 2N]`, good prime powers. -/

noncomputable section
open Polynomial Finset

namespace LaneC978

open LaneC976

/-- At a good prime `p ∤ D`, roots modulo `p^j` reduce injectively to roots modulo `p`. -/
theorem rho_pow_le_rho {f u v : ℤ[X]} {D : ℤ} (hB : f * u + derivative f * v = C D)
    {p : ℕ} (hp : p.Prime) (hpD : ¬ (p : ℤ) ∣ D) {j : ℕ} (hj : 1 ≤ j) :
    rho f (p ^ j) ≤ rho f p := by
  classical
  rw [rho, rho]
  refine card_le_card_of_injOn (fun r => r % p) ?_ ?_
  · intro r hr
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr ⊢
    have hpj : p ∣ p ^ j := dvd_pow_self p (Nat.one_le_iff_ne_zero.mp hj)
    exact ⟨Nat.mod_lt _ hp.pos, dvd_eval_mod hpj (by exact_mod_cast hr.2)⟩
  · intro r hr r' hr' h
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hr hr'
    simp only at h
    have h1 : ((p : ℕ) : ℤ) ^ (0 + 1) ∣ (r' : ℤ) - r := by
      rw [zero_add, pow_one]; exact Nat.modEq_iff_dvd.mp h
    have h2 := cluster hB hp (δ := 0) (by rw [zero_add, pow_one]; exact hpD) (show 0 + 1 ≤ j by omega)
      (x := (r : ℤ)) (y := (r' : ℤ)) (by exact_mod_cast hr.2) (by exact_mod_cast hr'.2) h1
    rw [Nat.sub_zero] at h2
    have h3 : r ≡ r' [MOD p ^ j] := Nat.modEq_iff_dvd.mpr (by exact_mod_cast h2)
    exact Nat.ModEq.eq_of_lt_of_lt h3 hr.1 hr'.1

/-- Lower bound for the Chinese remainder combination of residue conditions. -/
theorem card_res_ge (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (j : ℕ) (B : ℕ → Finset ℕ)
    (hB : ∀ p ∈ P, B p ⊆ range (p ^ j)) :
    ∏ p ∈ P, #(B p) ≤
      #((range (∏ p ∈ P, p ^ j)).filter fun x => ∀ p ∈ P, x % p ^ j ∈ B p) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    exact card_pos.mpr ⟨0, by simp⟩
  | insert q S hqS ih =>
    have hq := hP q (mem_insert_self q S)
    have hS : ∀ p ∈ S, p.Prime := fun p hp => hP p (mem_insert_of_mem hp)
    have ih' := ih hS (fun p hp => hB p (mem_insert_of_mem hp))
    set W := ∏ p ∈ S, p ^ j with hW
    have hW0 : 0 < W := prod_pos fun p hp => pow_pos (hS p hp).pos _
    have hcop : Nat.Coprime W (q ^ j) := by
      refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.pow _ _ ?_
      refine (Nat.coprime_primes (hS p hp) hq).mpr ?_
      rintro rfl; exact hqS hp
    set T := (range W).filter fun x => ∀ p ∈ S, x % p ^ j ∈ B p with hT
    rw [prod_insert hqS, prod_insert hqS, mul_comm (#(B q))]
    calc (∏ x ∈ S, #(B x)) * #(B q) ≤ #T * #(B q) := Nat.mul_le_mul_right _ ih'
      _ = #(T ×ˢ B q) := (card_product _ _).symm
      _ ≤ #((range (q ^ j * W)).filter fun x => ∀ p ∈ insert q S, x % p ^ j ∈ B p) := by
        refine card_le_card_of_injOn (s := T ×ˢ B q)
          (t := (range (q ^ j * W)).filter fun x => ∀ p ∈ insert q S, x % p ^ j ∈ B p)
          (fun xy => (Nat.chineseRemainder hcop xy.1 xy.2 : ℕ)) ?_ ?_
        · intro xy hxy
          simp only [coe_product, Set.mem_prod, hT, coe_filter, mem_range, Set.mem_ofPred_eq] at hxy
          have hcr := (Nat.chineseRemainder hcop xy.1 xy.2).2
          have hlt := Nat.chineseRemainder_lt_mul hcop xy.1 xy.2 hW0.ne' (pow_pos hq.pos _).ne'
          simp only [coe_filter, mem_range, Set.mem_ofPred_eq, forall_mem_insert]
          refine ⟨by rw [mul_comm]; exact hlt, ?_, fun p hp => ?_⟩
          · have h1 : (Nat.chineseRemainder hcop xy.1 xy.2 : ℕ) % q ^ j = xy.2 % q ^ j := hcr.2
            rw [h1, Nat.mod_eq_of_lt (mem_range.mp (hB q (mem_insert_self q S) hxy.2))]
            exact hxy.2
          · have h1 : (Nat.chineseRemainder hcop xy.1 xy.2 : ℕ) % W = xy.1 % W := hcr.1
            have hdvd : p ^ j ∣ W := dvd_prod_of_mem _ hp
            rw [← Nat.mod_mod_of_dvd _ hdvd, h1, Nat.mod_mod_of_dvd _ hdvd]
            exact hxy.1.2 p hp
        · intro xy hxy xy' hxy' h
          simp only [coe_product, Set.mem_prod, hT, coe_filter, mem_range, Set.mem_ofPred_eq] at hxy hxy'
          have hcr := (Nat.chineseRemainder hcop xy.1 xy.2).2
          have hcr' := (Nat.chineseRemainder hcop xy'.1 xy'.2).2
          simp only at h
          rw [h] at hcr
          have e1 : xy.1 % W = xy'.1 % W := hcr.1.symm.trans hcr'.1
          have e2 : xy.2 % q ^ j = xy'.2 % q ^ j := hcr.2.symm.trans hcr'.2
          rw [Nat.mod_eq_of_lt hxy.1.1, Nat.mod_eq_of_lt hxy'.1.1] at e1
          rw [Nat.mod_eq_of_lt (mem_range.mp (hB q (mem_insert_self q S) hxy.2)),
            Nat.mod_eq_of_lt (mem_range.mp (hB q (mem_insert_self q S) hxy'.2))] at e2
          exact Prod.ext e1 e2

/-- Lower bound for residue classes in `(N, 2N]`. -/
theorem count_Ioc_ge (N W : ℕ) (hW : 0 < W) (T : Finset ℕ) (hT : T ⊆ range W) :
    #T * (N / W) ≤ #((Ioc N (2 * N)).filter fun n => n % W ∈ T) := by
  classical
  set r := (N + 1) % W with hr
  rw [← card_range (N / W), ← card_product]
  refine card_le_card_of_injOn
    (fun ti => N + 1 + (ti.1 + W - r) % W + W * ti.2) ?_ ?_
  · intro ti hti
    simp only [coe_product, Set.mem_prod, coe_range, Set.mem_Iio] at hti
    have ht := mem_range.mp (hT hti.1)
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq]
    have hrW : r < W := Nat.mod_lt _ hW
    have hmod : (ti.1 + W - r) % W < W := Nat.mod_lt _ hW
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · have : W * ti.2 + W ≤ N := by
        have := Nat.div_mul_le_self N W
        nlinarith [hti.2]
      omega
    · -- the residue is `ti.1`
      have e1 : (N + 1 + (ti.1 + W - r) % W + W * ti.2) % W =
          ((N + 1) % W + (ti.1 + W - r) % W) % W := by
        rw [Nat.add_mul_mod_self_left, Nat.add_mod, Nat.add_mod ((N + 1) % W), Nat.mod_mod,
          Nat.mod_mod, Nat.mod_mod]
      rw [e1, ← hr, Nat.add_mod_mod, show r + (ti.1 + W - r) = ti.1 + W by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt ht]
      exact hti.1
  · intro ti hti ti' hti' h
    simp only [coe_product, Set.mem_prod, coe_range, Set.mem_Iio] at hti hti'
    simp only at h
    have hmod : (ti.1 + W - r) % W < W := Nat.mod_lt _ hW
    have hmod' : (ti'.1 + W - r) % W < W := Nat.mod_lt _ hW
    have h1 : (ti.1 + W - r) % W + W * ti.2 = (ti'.1 + W - r) % W + W * ti'.2 := by omega
    have h2 : ti.2 = ti'.2 := by
      have := congrArg (· / W) h1
      rwa [Nat.add_mul_div_left _ _ hW, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hmod,
        Nat.div_eq_of_lt hmod', zero_add, zero_add] at this
    have h3 : (ti.1 + W - r) % W = (ti'.1 + W - r) % W := by rw [h2] at h1; omega
    have ht := mem_range.mp (hT hti.1)
    have ht' := mem_range.mp (hT hti'.1)
    have hrW : r < W := Nat.mod_lt _ hW
    have h4 : ti.1 = ti'.1 := by
      have e : (ti.1 + W - r) % W + r ≡ (ti'.1 + W - r) % W + r [MOD W] := by rw [h3]
      have e1 : (ti.1 + W - r) % W + r ≡ ti.1 [MOD W] := by
        calc (ti.1 + W - r) % W + r ≡ (ti.1 + W - r) + r [MOD W] :=
              Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
          _ = ti.1 + W := by omega
          _ ≡ ti.1 [MOD W] := Nat.add_modEq_right
      have e2 : (ti'.1 + W - r) % W + r ≡ ti'.1 [MOD W] := by
        calc (ti'.1 + W - r) % W + r ≡ (ti'.1 + W - r) + r [MOD W] :=
              Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
          _ = ti'.1 + W := by omega
          _ ≡ ti'.1 [MOD W] := Nat.add_modEq_right
      exact Nat.ModEq.eq_of_lt_of_lt (e1.symm.trans (e.trans e2)) ht ht'
    exact Prod.ext h4 h2

/-- Upper bound for residue classes in `(N, 2N]`. -/
theorem count_Ioc_le (N P : ℕ) (hP : 0 < P) (R : Finset ℕ) :
    #((Ioc N (2 * N)).filter fun n => n % P ∈ R) ≤ #R * (N / P + 1) := by
  classical
  rw [← card_range (N / P + 1), ← card_product]
  refine card_le_card_of_injOn (fun n => (n % P, (n - (N + 1)) / P)) ?_ ?_
  · intro n hn
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hn
    simp only [coe_product, Set.mem_prod, coe_range, Set.mem_Iio]
    refine ⟨hn.2, ?_⟩
    have : (n - (N + 1)) / P ≤ N / P := Nat.div_le_div_right (by omega)
    omega
  · intro n hn n' hn' h
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hn hn'
    simp only [Prod.mk.injEq] at h
    have hu : n - (N + 1) ≡ n' - (N + 1) [MOD P] := by
      have h' : (n - (N + 1)) + (N + 1) ≡ (n' - (N + 1)) + (N + 1) [MOD P] := by
        rw [Nat.sub_add_cancel hn.1.1, Nat.sub_add_cancel hn'.1.1]; exact h.1
      exact Nat.ModEq.add_right_cancel' _ h'
    have hq : n - (N + 1) = n' - (N + 1) := by
      rw [← Nat.div_add_mod (n - (N + 1)) P, ← Nat.div_add_mod (n' - (N + 1)) P, h.2]
      rw [show (n - (N + 1)) % P = (n' - (N + 1)) % P from hu]
    omega

end LaneC978

end

/-! The step `Erdos978.erdos_978.variants.sub_one.R1.H1`: the small-prime sieve on `(N, 2N]`. -/

noncomputable section
open Polynomial Finset Filter

namespace LaneC978

open LaneC976

theorem prod_one_sub_ge {ι : Type*} (s : Finset ι) (x : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ x i)
    (h1 : ∀ i ∈ s, x i ≤ 1) : 1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have hx0 := h0 a (mem_insert_self a s)
    have hx1 := h1 a (mem_insert_self a s)
    have hs0 : 0 ≤ ∑ i ∈ s, x i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    have hp0 : 0 ≤ ∏ i ∈ s, (1 - x i) :=
      prod_nonneg fun i hi => by have := h1 i (mem_insert_of_mem hi); linarith
    nlinarith [mul_le_mul_of_nonneg_left ih' (show 0 ≤ 1 - x a by linarith)]

theorem dvd_of_mod {f : ℤ[X]} {P n : ℕ} (h : (P : ℤ) ∣ f.eval ((n : ℕ) : ℤ)) :
    (P : ℤ) ∣ f.eval ((n % P : ℕ) : ℤ) := dvd_eval_mod (dvd_refl P) h

set_option maxHeartbeats 4000000 in
open scoped Classical in
theorem sub_one_H1 : ∀ f : ℤ[X], Irreducible f → 2 < f.natDegree →
    (∀ p : ℕ, p.Prime → ∃ a : ℕ, ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (a : ℤ)) →
    ∃ A : ℕ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      N ≤ A * ((Finset.Ioc N (2 * N)).filter fun (n : ℕ) =>
        ∀ p : ℕ, p.Prime → p ≤ N → ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ)).card := by
  intro f hi hd hadm
  set k := f.natDegree with hk
  set j := k - 1 with hj
  have hj1 : 1 ≤ j := by omega
  have hfQ : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hi.isPrimitive (by omega))).mp hi
  obtain ⟨u, v, D, hD0, hB⟩ := exists_bezout f hfQ (by omega)
  have hlc0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hi.ne_zero
  set p1 := 4 * k + D.natAbs + f.leadingCoeff.natAbs + 1 with hp1
  -- roots at good prime powers
  have hgood : ∀ p, p.Prime → p1 < p → rho f (p ^ j) ≤ k := by
    intro p hp hpp1
    have hpD : ¬ (p : ℤ) ∣ D := by
      intro h; have := Nat.le_of_dvd (Int.natAbs_pos.mpr hD0) (Int.natCast_dvd.mp h); omega
    have hpa : ¬ (p : ℤ) ∣ f.leadingCoeff := by
      intro h; have := Nat.le_of_dvd (Int.natAbs_pos.mpr hlc0) (Int.natCast_dvd.mp h); omega
    exact (rho_pow_le_rho hB hp hpD hj1).trans (rho_le hp hpa)
  -- allowed residues mod `p^j`
  set Bs : ℕ → Finset ℕ := fun p => (range (p ^ j)).filter fun s =>
    ¬ (((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) with hBs
  have hBsub : ∀ p, Bs p ⊆ range (p ^ j) := fun p => filter_subset _ _
  have hBcard : ∀ p, #(Bs p) + rho f (p ^ j) = p ^ j := by
    intro p
    rw [hBs, rho, add_comm, card_filter_add_card_filter_not, card_range]
  have hBpos : ∀ p, p.Prime → 1 ≤ #(Bs p) := by
    intro p hp
    obtain ⟨a, ha⟩ := hadm p hp
    refine card_pos.mpr ⟨a % p ^ j, ?_⟩
    rw [hBs, mem_filter, mem_range]
    refine ⟨Nat.mod_lt _ (pow_pos hp.pos _), fun h => ha ?_⟩
    have h1 : ((p ^ j : ℕ) : ℤ) ∣ f.eval ((a % p ^ j : ℕ) : ℤ) := h
    have h2 := sub_dvd_eval_sub (a : ℤ) ((a % p ^ j : ℕ) : ℤ) f
    have h3 : ((p ^ j : ℕ) : ℤ) ∣ (a : ℤ) - ((a % p ^ j : ℕ) : ℤ) :=
      (Nat.modEq_iff_dvd.mp (Nat.mod_modEq a (p ^ j)))
    have := dvd_add (h3.trans h2) h1
    simp only [sub_add_cancel] at this
    push_cast at this; exact this
  -- the constant `c`
  set P1 := Nat.primesLE p1 with hP1
  set c : ℝ := (1 / 2) * ∏ p ∈ P1, (1 / (p : ℝ) ^ j) with hc
  have hc0 : 0 < c := by
    rw [hc]; refine mul_pos (by norm_num) (prod_pos fun p hp => ?_)
    have := (Nat.mem_primesLE.mp hp).2.pos; positivity
  set w := p1 + ⌈32 * k / c⌉₊ with hw
  set P := Nat.primesLE w with hP
  set W := ∏ p ∈ P, p ^ j with hW
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hW0 : 0 < W := prod_pos fun p hp => pow_pos (hPp p hp).pos _
  set G := (range W).filter fun x => ∀ p ∈ P, x % p ^ j ∈ Bs p with hG
  have hGcard := card_res_ge P hPp j Bs (fun p _ => hBsub p)
  -- density of `G`
  have hdens : c * W ≤ (#G : ℝ) := by
    have hsplit : P = P.filter (fun p => p ≤ p1) ∪ P.filter (fun p => ¬ p ≤ p1) :=
      (filter_union_filter_not_eq _ _).symm
    have hdisj := disjoint_filter_filter_not P P (fun p => p ≤ p1)
    have hratio : ∀ p ∈ P, (#(Bs p) : ℝ) = (p : ℝ) ^ j * (#(Bs p) / (p : ℝ) ^ j) := by
      intro p hp
      have : (0 : ℝ) < (p : ℝ) ^ j := by have := (hPp p hp).pos; positivity
      rw [mul_div_assoc', mul_div_cancel_left₀ _ this.ne']
    have hprod : (∏ p ∈ P, (#(Bs p) : ℝ)) = W * ∏ p ∈ P, (#(Bs p) / (p : ℝ) ^ j) := by
      rw [prod_congr rfl hratio, prod_mul_distrib, hW]; push_cast; rfl
    have hlow1 : ∏ p ∈ P.filter (fun p => p ≤ p1), (#(Bs p) / (p : ℝ) ^ j) ≥
        ∏ p ∈ P1, (1 / (p : ℝ) ^ j) := by
      have hsub : P.filter (fun p => p ≤ p1) ⊆ P1 := by
        intro p hp; rw [mem_filter, hP, Nat.mem_primesLE] at hp
        rw [hP1, Nat.mem_primesLE]; exact ⟨hp.2, hp.1.2⟩
      have heq : P.filter (fun p => p ≤ p1) = P1 := by
        refine Subset.antisymm hsub fun p hp => ?_
        rw [hP1, Nat.mem_primesLE] at hp
        rw [mem_filter, hP, Nat.mem_primesLE]; exact ⟨⟨by omega, hp.2⟩, hp.1⟩
      calc ∏ p ∈ P1, (1 / (p : ℝ) ^ j) = ∏ p ∈ P.filter (fun p => p ≤ p1), (1 / (p : ℝ) ^ j) := by
            rw [heq]
        _ ≤ ∏ p ∈ P.filter (fun p => p ≤ p1), (#(Bs p) / (p : ℝ) ^ j) := by
            refine prod_le_prod (fun p _ => by positivity) fun p hp => ?_
            have := hBpos p (hPp p (mem_filter.mp hp).1)
            gcongr
            exact_mod_cast this
    have hlow2 : ∏ p ∈ P.filter (fun p => ¬ p ≤ p1), (#(Bs p) / (p : ℝ) ^ j) ≥ 1 / 2 := by
      have hge : ∀ p ∈ P.filter (fun p => ¬ p ≤ p1),
          1 - k / (p : ℝ) ^ 2 ≤ (#(Bs p) / (p : ℝ) ^ j) := by
        intro p hp
        have hpp := hPp p (mem_filter.mp hp).1
        have hpbig : p1 < p := by have := (mem_filter.mp hp).2; omega
        have hr := hgood p hpp hpbig
        have hb := hBcard p
        have hpj : (0 : ℝ) < (p : ℝ) ^ j := by have := hpp.pos; positivity
        have hp2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ j := pow_le_pow_right₀ (by exact_mod_cast hpp.one_lt.le)
          (by omega)
        have hbr : (#(Bs p) : ℝ) = (p : ℝ) ^ j - rho f (p ^ j) := by
          have : ((#(Bs p) + rho f (p ^ j) : ℕ) : ℝ) = ((p ^ j : ℕ) : ℝ) := by rw [hb]
          push_cast at this; linarith
        rw [hbr, sub_div, div_self hpj.ne']
        have h1 : (rho f (p ^ j) : ℝ) / (p : ℝ) ^ j ≤ k / (p : ℝ) ^ 2 := by
          have hr' : (rho f (p ^ j) : ℝ) ≤ k := by exact_mod_cast hr
          calc (rho f (p ^ j) : ℝ) / (p : ℝ) ^ j ≤ k / (p : ℝ) ^ j := by gcongr
            _ ≤ k / (p : ℝ) ^ 2 := by
                apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by have := hpp.pos; positivity) hp2
        linarith
      have hsum : ∑ p ∈ P.filter (fun p => ¬ p ≤ p1), (k : ℝ) / (p : ℝ) ^ 2 ≤ 1 / 2 := by
        have hsub : P.filter (fun p => ¬ p ≤ p1) ⊆ Icc (p1 + 1) w := by
          intro p hp
          rw [mem_filter, hP, Nat.mem_primesLE] at hp
          rw [mem_Icc]; exact ⟨by omega, hp.1.1⟩
        calc ∑ p ∈ P.filter (fun p => ¬ p ≤ p1), (k : ℝ) / (p : ℝ) ^ 2
            ≤ ∑ p ∈ Icc (p1 + 1) w, (k : ℝ) / (p : ℝ) ^ 2 :=
              sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
          _ = k * ∑ p ∈ Icc (p1 + 1) w, (1 : ℝ) / (p : ℝ) ^ 2 := by
              rw [mul_sum]; refine sum_congr rfl fun p _ => by ring
          _ ≤ k * (2 / ((p1 + 1 : ℕ) : ℝ)) := by
              gcongr; exact sum_inv_sq_le' (p1 + 1) w (by omega)
          _ ≤ 1 / 2 := by
              have hp1r : (4 * k + 1 : ℝ) ≤ ((p1 + 1 : ℕ) : ℝ) := by
                have : 4 * k + 1 ≤ p1 + 1 := by omega
                exact_mod_cast this
              rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith
      have hx1 : ∀ p ∈ P.filter (fun p => ¬ p ≤ p1), (k : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
        intro p hp
        have hpp := hPp p (mem_filter.mp hp).1
        have hpbig : p1 < p := by have := (mem_filter.mp hp).2; omega
        have hpr : (4 * k : ℝ) ≤ p := by exact_mod_cast (show 4 * k ≤ p by omega)
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
        rw [div_le_one (by positivity)]
        nlinarith
      have := prod_one_sub_ge (P.filter (fun p => ¬ p ≤ p1)) (fun p => (k : ℝ) / (p : ℝ) ^ 2)
        (fun _ _ => by positivity) hx1
      have hmono : ∏ p ∈ P.filter (fun p => ¬ p ≤ p1), (1 - (k : ℝ) / (p : ℝ) ^ 2) ≤
          ∏ p ∈ P.filter (fun p => ¬ p ≤ p1), (#(Bs p) / (p : ℝ) ^ j) :=
        prod_le_prod (fun p hp => by have := hx1 p hp; linarith) hge
      linarith
    have hpos1 : 0 ≤ ∏ p ∈ P1, (1 / (p : ℝ) ^ j) := prod_nonneg fun p _ => by positivity
    have hGr : (∏ p ∈ P, (#(Bs p) : ℝ)) ≤ (#G : ℝ) := by exact_mod_cast hGcard
    rw [hprod, hsplit, prod_union hdisj] at hGr
    rw [hc]
    have hW0r : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    have : (1 / 2) * ∏ p ∈ P1, (1 / (p : ℝ) ^ j) ≤
        (∏ p ∈ P.filter (fun p => p ≤ p1), (#(Bs p) / (p : ℝ) ^ j)) *
          ∏ p ∈ P.filter (fun p => ¬ p ≤ p1), (#(Bs p) / (p : ℝ) ^ j) := by
      rw [mul_comm]
      exact mul_le_mul hlow1 hlow2 (by norm_num) (le_trans hpos1 hlow1)
    nlinarith [mul_le_mul_of_nonneg_left this hW0r]
  -- the count
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (pi_small k 1 le_rfl c hc0)
  set A := ⌈4 / c⌉₊ + 1 with hA
  refine ⟨A, by omega, max N1 (max (4 * W) (w + 1)), fun N hN => ?_⟩
  have hNN1 : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hNW : 4 * W ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNw : w + 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  set Good := (Finset.Ioc N (2 * N)).filter fun (n : ℕ) =>
    ∀ p : ℕ, p.Prime → p ≤ N → ¬ (p : ℤ) ^ (f.natDegree - 1) ∣ f.eval (n : ℤ) with hGood
  set Cand := (Ioc N (2 * N)).filter fun n => n % W ∈ G with hCand
  set Bad := ((Ioc w N).filter Nat.Prime).biUnion fun p =>
    (Ioc N (2 * N)).filter fun n => n % p ^ j ∈ (range (p ^ j)).filter
      fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ) with hBad
  have hsub : Cand \ Bad ⊆ Good := by
    intro n hn
    rw [Finset.mem_sdiff] at hn
    obtain ⟨hnC, hnB⟩ := hn
    rw [hCand, mem_filter] at hnC
    rw [hGood, mem_filter]
    refine ⟨hnC.1, fun p hp hpN hdvd => ?_⟩
    have hdvd' : ((p ^ j : ℕ) : ℤ) ∣ f.eval ((n : ℕ) : ℤ) := by push_cast; exact hdvd
    by_cases hpw : p ≤ w
    · have hpP : p ∈ P := by rw [hP, Nat.mem_primesLE]; exact ⟨hpw, hp⟩
      have hG' := (mem_filter.mp hnC.2).2 p hpP
      rw [Nat.mod_mod_of_dvd _ (dvd_prod_of_mem _ hpP)] at hG'
      rw [hBs, mem_filter] at hG'
      exact hG'.2 (dvd_of_mod hdvd')
    · apply hnB
      rw [hBad, mem_biUnion]
      refine ⟨p, ?_, ?_⟩
      · rw [mem_filter, mem_Ioc]; exact ⟨⟨by omega, hpN⟩, hp⟩
      · rw [mem_filter]
        refine ⟨hnC.1, ?_⟩
        rw [mem_filter, mem_range]
        exact ⟨Nat.mod_lt _ (pow_pos hp.pos _), dvd_of_mod hdvd'⟩
  have hcount : (#Cand : ℝ) ≤ #Good + #Bad := by
    have h1 := card_le_card_sdiff_add_card (s := Cand) (t := Bad)
    have h2 := card_le_card hsub
    have : #Cand ≤ #Good + #Bad := by omega
    exact_mod_cast this
  have hCand_ge : #G * (N / W) ≤ #Cand := count_Ioc_ge N W hW0 G (filter_subset _ _)
  have hBad_le : (#Bad : ℝ) ≤ k * N * (2 / ((w + 1 : ℕ) : ℝ)) + k * Nat.primeCounting (1 * N) := by
    have h1 : #Bad ≤ ∑ p ∈ (Ioc w N).filter Nat.Prime, #((Ioc N (2 * N)).filter fun n =>
        n % p ^ j ∈ (range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) :=
      card_biUnion_le
    have h2 : ∀ p ∈ (Ioc w N).filter Nat.Prime, (#((Ioc N (2 * N)).filter fun n =>
        n % p ^ j ∈ (range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) : ℝ) ≤
        k * (N / (p : ℝ) ^ 2 + 1) := by
      intro p hp
      rw [mem_filter, mem_Ioc] at hp
      have hpp := hp.2
      have hc1 := count_Ioc_le N (p ^ j) (pow_pos hpp.pos _)
        ((range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ))
      have hrho : #((range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) ≤ k := by
        have := hgood p hpp (by omega)
        rw [rho] at this
        exact this
      have hp2 : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ j := pow_le_pow_right₀ (by exact_mod_cast hpp.one_lt.le)
        (by omega)
      have hp20 : (0 : ℝ) < (p : ℝ) ^ 2 := by have := hpp.pos; positivity
      have hdiv : ((N / p ^ j : ℕ) : ℝ) ≤ N / (p : ℝ) ^ 2 := by
        refine (Nat.cast_div_le).trans ?_
        push_cast
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hp20 hp2
      calc (#((Ioc N (2 * N)).filter fun n =>
            n % p ^ j ∈ (range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) : ℝ)
          ≤ ((#((range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) *
              (N / p ^ j + 1) : ℕ) : ℝ) := by exact_mod_cast hc1
        _ ≤ k * (N / (p : ℝ) ^ 2 + 1) := by
            push_cast
            gcongr
            exact_mod_cast hrho
    have h3 : ∑ p ∈ (Ioc w N).filter Nat.Prime, (k : ℝ) * (N / (p : ℝ) ^ 2 + 1) ≤
        k * N * (2 / ((w + 1 : ℕ) : ℝ)) + k * Nat.primeCounting (1 * N) := by
      have e : ∑ p ∈ (Ioc w N).filter Nat.Prime, (k : ℝ) * (N / (p : ℝ) ^ 2 + 1) =
          k * N * ∑ p ∈ (Ioc w N).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2 +
            k * #((Ioc w N).filter Nat.Prime) := by
        rw [show (∑ p ∈ (Ioc w N).filter Nat.Prime, (k : ℝ) * (N / (p : ℝ) ^ 2 + 1)) =
            ∑ p ∈ (Ioc w N).filter Nat.Prime, ((k : ℝ) * N * (1 / (p : ℝ) ^ 2) + k) from
          sum_congr rfl (fun p _ => by ring), sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
        ring
      rw [e]
      have hs1 : ∑ p ∈ (Ioc w N).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 2 / ((w + 1 : ℕ) : ℝ) := by
        refine le_trans ?_ (sum_inv_sq_le' (w + 1) N (by omega))
        refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => by positivity)
        rw [mem_filter, mem_Ioc] at hp; rw [mem_Icc]; omega
      have hs2 : #((Ioc w N).filter Nat.Prime) ≤ Nat.primeCounting (1 * N) := by
        rw [one_mul, ← Nat.primesLE_card_eq_primeCounting]
        refine card_le_card fun p hp => ?_
        rw [mem_filter, mem_Ioc] at hp; rw [Nat.mem_primesLE]; exact ⟨hp.1.2, hp.2⟩
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have hs2r : (#((Ioc w N).filter Nat.Prime) : ℝ) ≤ Nat.primeCounting (1 * N) := by
        exact_mod_cast hs2
      have := mul_le_mul_of_nonneg_left hs1 (mul_nonneg hk0 hN0)
      have := mul_le_mul_of_nonneg_left hs2r hk0
      linarith
    have h1' : (#Bad : ℝ) ≤ ∑ p ∈ (Ioc w N).filter Nat.Prime, (#((Ioc N (2 * N)).filter fun n =>
        n % p ^ j ∈ (range (p ^ j)).filter fun s => ((p ^ j : ℕ) : ℤ) ∣ f.eval ((s : ℕ) : ℤ)) : ℝ) := by
      exact_mod_cast h1
    exact h1'.trans ((sum_le_sum h2).trans h3)
  -- final arithmetic
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW0
  have hNWr : (4 * W : ℝ) ≤ N := by exact_mod_cast hNW
  have hdivlow : (N : ℝ) / W - 1 ≤ ((N / W : ℕ) : ℝ) := by
    have h := Nat.lt_div_mul_add (a := N) hW0
    have h' : (N : ℝ) < ((N / W : ℕ) : ℝ) * W + W := by exact_mod_cast h
    rw [div_sub_one hWr.ne', div_le_iff₀ hWr]; linarith
  have hCr : c * N - c * W ≤ (#Cand : ℝ) := by
    have h1 : ((#G * (N / W) : ℕ) : ℝ) ≤ #Cand := by exact_mod_cast hCand_ge
    push_cast at h1
    have h2 : c * W * ((N : ℝ) / W - 1) ≤ (#G : ℝ) * ((N / W : ℕ) : ℝ) := by
      have hN0 : (0 : ℝ) ≤ (N : ℝ) / W - 1 := by
        rw [sub_nonneg, le_div_iff₀ hWr]; linarith
      calc c * W * ((N : ℝ) / W - 1) ≤ (#G : ℝ) * ((N : ℝ) / W - 1) :=
            mul_le_mul_of_nonneg_right hdens hN0
        _ ≤ (#G : ℝ) * ((N / W : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hdivlow (Nat.cast_nonneg _)
    have h3 : c * W * ((N : ℝ) / W - 1) = c * N - c * W := by field_simp
    linarith
  have hpi := hN1 N hNN1
  have hwr : 32 * k / c ≤ ((w + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil (32 * k / c)
    have h' : ((⌈32 * k / c⌉₊ : ℕ) : ℝ) ≤ ((w + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show ⌈32 * k / c⌉₊ ≤ w + 1 by omega)
    linarith
  have hw1 : (0 : ℝ) < ((w + 1 : ℕ) : ℝ) := by positivity
  have hkw : (k : ℝ) * (2 / ((w + 1 : ℕ) : ℝ)) ≤ c / 16 := by
    rw [mul_div_assoc', div_le_iff₀ hw1]
    rw [div_le_iff₀ hc0] at hwr
    nlinarith
  have hBadr : (#Bad : ℝ) ≤ c / 16 * N + c / 4 * N := by
    have := mul_le_mul_of_nonneg_right hkw (show (0 : ℝ) ≤ N by positivity)
    linarith [hBad_le]
  have hGoodr : c / 4 * N ≤ (#Good : ℝ) := by
    have hcW : c * W ≤ c / 4 * N := by nlinarith
    linarith
  have hAr : 4 / c ≤ (A : ℝ) := by
    have := Nat.le_ceil (4 / c); rw [hA]; push_cast; linarith
  have : (N : ℝ) ≤ A * #Good := by
    calc (N : ℝ) = 4 / c * (c / 4 * N) := by field_simp
      _ ≤ A * #Good := by
          apply mul_le_mul hAr hGoodr (by positivity) (by positivity)
  exact_mod_cast this

end LaneC978

end

theorem OMA.solution : OMA.R_Erdos978_erdos_978_variants_sub_one_R1.H1 := LaneC978.sub_one_H1
