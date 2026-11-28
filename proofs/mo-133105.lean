import OMAStatements.S_mo_133105
import Mathlib

namespace OMA.S_mo_133105

open scoped BigOperators

private noncomputable def translate (j : ℕ) (x : Seq) : Seq :=
  x.compContinuous ⟨fun n => n + j, continuous_of_discreteTopology⟩

private theorem translate_eq (j : ℕ) (x : Seq) :
    translate (j + 1) x = shift (translate j x) := by
  apply BoundedContinuousFunction.ext
  intro n
  change x (n + (j + 1)) = x (n + 1 + j)
  exact congrArg x (by omega)

private theorem translate_preserves (p : Seminorm ℝ Seq) (hp : admissible p)
    (x : Seq) (j : ℕ) : p (translate j x) = p x := by
  induction j with
  | zero =>
    have hz : translate 0 x = x :=
      BoundedContinuousFunction.ext fun n => congrArg x (Nat.add_zero n)
    rw [hz]
  | succ j ih => rw [translate_eq, hp.1, ih]

private noncomputable def residue (d r : ℕ) : Seq :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => if n % d = r then 1 else 0) 1 (by
    intro n
    split <;> simp)

private theorem residue_value (d r n : ℕ) :
    residue d r n = if n % d = r then 1 else 0 := rfl

private theorem translate_sum (d r : ℕ) (hr : r < d) :
    (∑ j ∈ Finset.range d, translate j (residue d r)) = 1 := by
  apply BoundedContinuousFunction.ext
  intro n
  let ev : Seq →+ ℝ :=
    { toFun := fun x => x n
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev _ = 1
  rw [map_sum]
  change (∑ j ∈ Finset.range d, if (n + j) % d = r then (1 : ℝ) else 0) = 1
  let j := (r + d - n % d) % d
  have hd : 0 < d := by omega
  have hj : j < d := Nat.mod_lt _ hd
  have hn : n % d < d := Nat.mod_lt _ hd
  have htarget : (n + j) % d = r := by
    dsimp [j]
    rw [Nat.add_mod n]
    simp only [Nat.mod_mod]
    have hsum : n % d + (r + d - n % d) = r + d := by omega
    calc
      (n % d + (r + d - n % d) % d) % d = (n % d + (r + d - n % d)) % d := by
        simpa only [Nat.mod_mod] using (Nat.add_mod (n % d) (r + d - n % d) d).symm
      _ = r := by rw [hsum]; simp [Nat.mod_eq_of_lt hr]
  rw [Finset.sum_eq_single j]
  · simp [htarget]
  · intro k hk hkj
    have hk' : k < d := Finset.mem_range.mp hk
    have hne : (n + k) % d ≠ r := by
      intro hkval
      have heq : n + k ≡ n + j [MOD d] := hkval.trans htarget.symm
      have hkj' : k ≡ j [MOD d] := Nat.ModEq.add_left_cancel' n heq
      exact hkj (by simpa [Nat.ModEq, Nat.mod_eq_of_lt hk', Nat.mod_eq_of_lt hj] using hkj')
    simp [hne]
  · exact fun h => (h (Finset.mem_range.mpr hj)).elim

/-- The translates of each residue class partition the indices. -/
private theorem residue_pos (p : Seminorm ℝ Seq) (hp : admissible p) (hp0 : p ≠ 0)
    (d r : ℕ) (hr : r < d) : 0 < p (residue d r) := by
  by_contra! h
  have hpone : 0 < p (1 : Seq) := by
    by_contra! hOne
    have hzero : p (1 : Seq) = 0 := le_antisymm hOne (apply_nonneg p _)
    apply hp0
    ext x
    have hprod := hp.2 (1 : Seq) x
    rw [one_mul, hzero, zero_mul] at hprod
    simpa using le_antisymm hprod (apply_nonneg p x)
  have hb : p (1 : Seq) ≤ ∑ j ∈ Finset.range d, p (translate j (residue d r)) := by
    rw [← translate_sum d r hr]
    exact Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
  simp only [translate_preserves p hp, le_antisymm h (apply_nonneg p _),
    Finset.sum_const_zero] at hb
  exact hpone.not_ge hb

private def valuation (k : ℕ) : ℕ := (k + 1).factorization 2

private theorem valuation_le (k : ℕ) : valuation k ≤ k + 1 := by
  have hv : 2 ^ valuation k ∣ k + 1 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.succ_ne_zero k)).mpr le_rfl
  have hb := Nat.le_of_dvd (Nat.succ_pos k) hv
  have hl := (valuation k).lt_two_pow_self
  omega

/-- The even steps encode the valuation and the odd steps restore exponential growth. -/
private def growing (n : ℕ) : ℕ :=
  let k := n / 2
  if n % 2 = 0 then 2 ^ (2 * k + 2)
  else 2 ^ (2 * k + 2) + 2 ^ (2 * k + 2 - valuation k)

private theorem growing_even (k : ℕ) : growing (2 * k) = 2 ^ (2 * k + 2) := by
  have hdiv : 2 * k / 2 = k := by omega
  have hmod : 2 * k % 2 = 0 := by omega
  simp [growing, hdiv, hmod]

private theorem growing_odd (k : ℕ) :
    growing (2 * k + 1) = 2 ^ (2 * k + 2) + 2 ^ (2 * k + 2 - valuation k) := by
  have hdiv : (2 * k + 1) / 2 = k := by omega
  have hmod : (2 * k + 1) % 2 = 1 := by omega
  simp [growing, hdiv, hmod]

private theorem growing_strict : StrictMono growing := by
  apply strictMono_nat_of_lt_succ
  intro n
  let k := n / 2
  have hk : n = 2 * k ∨ n = 2 * k + 1 := by dsimp [k]; omega
  rcases hk with h | h
  · rw [h, growing_even, growing_odd]
    have : 0 < (2 : ℕ) ^ (2 * k + 2 - valuation k) := by positivity
    omega
  · have hnext : growing (2 * k + 1 + 1) = 2 ^ (2 * k + 2) * 4 := by
      rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, growing_even]
      rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by omega, pow_add]
      rfl
    rw [h, growing_odd, hnext]
    have hb : (2 : ℕ) ^ (2 * k + 2 - valuation k) ≤ 2 ^ (2 * k + 2) :=
      pow_le_pow_right₀ (by decide) (Nat.sub_le ..)
    have : 0 < (2 : ℕ) ^ (2 * k + 2) := by positivity
    omega

private theorem growing_bound (n : ℕ) : 2 ^ n ≤ growing n := by
  let k := n / 2
  have hk : n = 2 * k ∨ n = 2 * k + 1 := by dsimp [k]; omega
  rcases hk with h | h
  · rw [h, growing_even]
    exact pow_le_pow_right₀ (by decide) (by omega)
  · rw [h, growing_odd]
    exact (pow_le_pow_right₀ (by decide) (by omega)).trans (Nat.le_add_right ..)

private theorem selected_value (v n : ℕ) (hn : n % (4 * 2 ^ v) = 2 * (2 ^ v - 1)) :
    ratio growing growing_strict.monotone n = (2 : ℝ) ^ v / (2 ^ v + 1) := by
  let b : ℕ := 2 ^ v
  let q := n / (4 * b)
  have hb : 0 < b := by positivity
  have hn' : n = 2 * (b * (2 * q + 1) - 1) := by
    have hd := Nat.mod_add_div n (4 * b)
    change n % (4 * b) = 2 * (b - 1) at hn
    rw [hn] at hd
    change 2 * (b - 1) + 4 * b * q = n at hd
    have hring : 2 * (b * (2 * q + 1)) = 4 * b * q + 2 * b := by ring
    have hpos : 0 < b * (2 * q + 1) := by positivity
    omega
  let k := b * (2 * q + 1) - 1
  have hp : 0 < b * (2 * q + 1) := by positivity
  have hk : k + 1 = b * (2 * q + 1) := Nat.sub_add_cancel (by omega)
  have hv : valuation k = v := by
    unfold valuation
    rw [hk, Nat.factorization_mul (by positivity) (by positivity)]
    have hodd : ¬ 2 ∣ (2 * q + 1) := by omega
    simp [b, Nat.prime_two.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hodd]
  change (growing n : ℝ) / (growing (n + 1) : ℝ) = _
  rw [hn', growing_even k, growing_odd k, hv]
  push_cast
  have hle : v ≤ 2 * k + 2 := by have := valuation_le k; omega
  rw [show (2 : ℝ) ^ (2 * k + 2) = 2 ^ (2 * k + 2 - v) * 2 ^ v by
    rw [← pow_add, Nat.sub_add_cancel hle]]
  have hpos : 0 < (2 : ℝ) ^ (2 * k + 2 - v) := by positivity
  have hpos' : 0 < (2 : ℝ) ^ v + 1 := by positivity
  field_simp

private theorem ratio_lower (p : Seminorm ℝ Seq) (hp : admissible p) (hp0 : p ≠ 0) :
    1 ≤ p (ratio growing growing_strict.monotone) := by
  let x := ratio growing growing_strict.monotone
  have hbounds (v : ℕ) : (2 : ℝ) ^ v / (2 ^ v + 1) ≤ p x := by
    let d : ℕ := 4 * 2 ^ v
    let r : ℕ := 2 * (2 ^ v - 1)
    let e := residue d r
    have hpow : 0 < (2 : ℕ) ^ v := by positivity
    have hr : r < d := by dsimp [r, d]; omega
    have he : 0 < p e := residue_pos p hp hp0 d r hr
    have hc : 0 ≤ (2 : ℝ) ^ v / (2 ^ v + 1) := by positivity
    have hmul : x * e = ((2 : ℝ) ^ v / (2 ^ v + 1)) • e := by
      apply BoundedContinuousFunction.ext
      intro n
      rw [BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.smul_apply]
      change x n * residue d r n = _ * residue d r n
      rw [residue_value]
      by_cases h : n % d = r
      · rw [if_pos h, selected_value v n h]
      · simp [h]
    have hh := hp.2 x e
    rw [hmul, map_smul_eq_mul, Real.norm_of_nonneg hc] at hh
    exact le_of_mul_le_mul_right hh he
  by_contra! h
  obtain ⟨v, hv⟩ := exists_nat_gt (p x / (1 - p x))
  have hvpow : (v : ℝ) ≤ (2 : ℝ) ^ v := by
    exact_mod_cast (Nat.le_of_lt v.lt_two_pow_self)
  have hb := (div_le_iff₀ (show 0 < (2 : ℝ) ^ v + 1 by positivity)).mp (hbounds v)
  have hv' := (div_lt_iff₀ (sub_pos.mpr h)).mp (hv.trans_le hvpow)
  linarith

end OMA.S_mo_133105

open OMA.S_mo_133105 in
theorem OMA.solution : type_of% @OMA.S_mo_133105.main := by
  refine ⟨⟨growing, growing_strict, growing_bound, ratio_lower⟩, ?_, ?_⟩
  · intro p hp
    constructor
    · intro h
      by_contra hp0
      have hbad := h growing growing_strict (fun n => lt_of_lt_of_le (by positivity) (growing_bound n))
        ⟨1, 2, by norm_num, by norm_num, fun n => by
          simpa using (show (2 : ℝ) ^ n ≤ (growing n : ℝ) by exact_mod_cast growing_bound n)⟩
      exact hbad.not_ge (ratio_lower p hp hp0)
    · rintro rfl
      simp
  · refine ⟨fun n => 2 * (n + 1), fun n => n + 1, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      dsimp
      omega
    · intro a b hab
      dsimp
      omega
    · intro n
      change 0 < n + 1 ∧ n + 1 < 2 * (n + 1)
      omega
    · apply BoundedContinuousFunction.ext
      intro n
      change (↑(2 * (n + 1)) : ℝ) / ↑(2 * (n + 1 + 1)) = (↑(n + 1) : ℝ) / ↑(n + 1 + 1)
      push_cast
      have h : 0 < (n : ℝ) + 1 + 1 := by positivity
      field_simp
      <;> ring