import OMAReductions.R_OeisA287616_conjecture_R1_H2_R1

/-! Two elementary repairs of the heptagonal coordinate, corresponding to
Lemma 9(1) and (4) of Cao, Guo, Qiu, Feng and Gao, arXiv:2606.26035.
The middle coordinate stays unchanged, and the inverse scaled map
preserves primitivity. -/

namespace OMA.R_OeisA287616_conjecture_R1_H2_R1_H2_R1

private def allOdd (u v w : ℕ) : Prop := u % 2 = 1 ∧ v % 2 = 1 ∧ w % 2 = 1

private def score (u v w : ℕ) : ℕ :=
  let odd := u % 2 = 1 ∧ v % 2 = 1 ∧ w % 2 = 1
  let badV := if odd ∧ v % 6 = 1 then 0 else 1
  let badW := if odd ∧ w % 10 = 1 then 0 else 1
  let regretV := if odd ∧ u % 4 ≠ v % 4 then 0 else badV
  let regretW := if (u + w) % 3 = 0 then 0 else badW
  let evenPenalty := if odd then 0 else 2
  5 * (badV + badW) + regretV + regretW + evenPenalty

private def rank (n u v w : ℕ) : ℕ :=
  score u v w * (3 * (120 * n + 23) + 1) + u + v + w

private theorem rank_drop {n u v w x y z : ℕ}
    (h : 15 * x ^ 2 + 5 * y ^ 2 + 3 * z ^ 2 = 120 * n + 23)
    (hscore : score x y z < score u v w) : rank n x y z < rank n u v w := by
  have hx := Nat.le_self_pow (by decide : 2 ≠ 0) x
  have hy := Nat.le_self_pow (by decide : 2 ≠ 0) y
  have hz := Nat.le_self_pow (by decide : 2 ≠ 0) z
  have hsum : x + y + z < 3 * (120 * n + 23) + 1 := by omega
  have hscale := Nat.mul_le_mul_right (3 * (120 * n + 23) + 1)
    (show score x y z + 1 ≤ score u v w by omega)
  rw [Nat.add_mul, Nat.one_mul] at hscale
  unfold rank
  omega

private theorem third_residue {n u v w : ℕ}
    (h : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23)
    (hw : w % 2 = 1) : w % 10 = 1 ∨ w % 10 = 9 := by
  have hmod : (3 * w ^ 2) % 5 = 3 := by omega
  rw [Nat.mul_mod, Nat.pow_mod] at hmod
  have hb : w % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases hr : w % 5 <;> norm_num [hr] at hmod <;> omega

private theorem not_three_middle {n u v w : ℕ}
    (h : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23) : ¬ 3 ∣ v := by
  intro hd
  have hm : (5 * v ^ 2) % 3 = 2 := by omega
  rw [Nat.mul_mod, Nat.pow_mod, Nat.dvd_iff_mod_eq_zero.mp hd] at hm
  norm_num at hm

private theorem abs_odd {a : ℤ} (h : a % 2 = 1) : a.natAbs % 2 = 1 := by
  by_cases hn : 0 ≤ a
  · have e := Int.natAbs_of_nonneg hn
    omega
  · have e : (a.natAbs : ℤ) = -a := by
      rw [← Int.natAbs_neg a, Int.natAbs_of_nonneg (by omega : 0 ≤ -a)]
    omega

private theorem signed_uw_repair {n u v w : ℕ}
    (hq : 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23)
    (hp : u.gcd (v.gcd w) = 1) (ho : allOdd u v w) (hw : w % 10 = 9)
    (hwindow : (u + w) % 3 = 0 ∨ (u % 3 = w % 3 ∧ 5 * u < 2 * w)) :
    ∃ x z : ℕ, 15 * x ^ 2 + 5 * v ^ 2 + 3 * z ^ 2 = 120 * n + 23 ∧
      x.gcd (v.gcd z) = 1 ∧ x % 2 = 1 ∧ z % 10 = 1 := by
  obtain ⟨hu₂, _, hw₂⟩ := ho
  let U : ℤ := if (u + w) % 3 = 0 then -(u : ℤ) else u
  let a : ℤ := (-2 * U - w) / 3
  let b : ℤ := (5 * U - 2 * w) / 3
  have hsign : U = -(u : ℤ) ∨ U = u := by
    dsimp [U]
    split_ifs <;> simp
  have ha : 3 * a = -2 * U - w := by
    dsimp [a, U]
    split_ifs with h
    · omega
    · have hh := hwindow.resolve_left h
      omega
  have hb : 3 * b = 5 * U - 2 * w := by
    dsimp [b, U]
    split_ifs with h
    · omega
    · have hh := hwindow.resolve_left h
      omega
  have hbn : b < 0 := by
    by_cases h : (u + w) % 3 = 0
    · have hU : U = -(u : ℤ) := if_pos h
      omega
    · have hU : U = (u : ℤ) := if_neg h
      have hh := (hwindow.resolve_left h).2
      omega
  have hza : (b.natAbs : ℤ) = -b := by
    rw [← Int.natAbs_neg b, Int.natAbs_of_nonneg (by omega : 0 ≤ -b)]
  have ha₂ : a.natAbs % 2 = 1 := abs_odd (by rcases hsign with h | h <;> omega)
  have hb₁₀ : b.natAbs % 10 = 1 := by
    rcases hsign with h | h <;> omega
  have e1 : -2 * a + b = 3 * U := by omega
  have e2 : -5 * a - 2 * b = 3 * (w : ℤ) := by omega
  have hprim : a.natAbs.gcd (v.gcd b.natAbs) = 1 := by
    by_contra hne
    obtain ⟨p, prime, hd⟩ := Nat.exists_prime_and_dvd hne
    have daN := hd.trans (Nat.gcd_dvd_left a.natAbs (v.gcd b.natAbs))
    have dvz := hd.trans (Nat.gcd_dvd_right a.natAbs (v.gcd b.natAbs))
    have dv := dvz.trans (Nat.gcd_dvd_left v b.natAbs)
    have dbN := dvz.trans (Nat.gcd_dvd_right v b.natAbs)
    have da : (p : ℤ) ∣ a := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr daN)
    have db : (p : ℤ) ∣ b := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr dbN)
    have dU : (p : ℤ) ∣ 3 * U := by
      rw [← e1]
      exact dvd_add (dvd_mul_of_dvd_right da _) db
    have du : p ∣ 3 * u := Int.natCast_dvd_natCast.mp (by
      push_cast
      rcases hsign with h | h
      · rw [h, mul_neg] at dU
        exact dvd_neg.mp dU
      · rwa [h] at dU)
    have dw : p ∣ 3 * w := Int.natCast_dvd_natCast.mp (by
      push_cast
      rw [← e2]
      exact dvd_sub (dvd_mul_of_dvd_right da _) (dvd_mul_of_dvd_right db _))
    have d3 : ¬ p ∣ 3 := by
      intro d
      have peq := (Nat.prime_dvd_prime_iff_eq prime Nat.prime_three).mp d
      exact not_three_middle hq (peq ▸ dv)
    have both : p ∣ u.gcd (v.gcd w) := Nat.dvd_gcd
      ((prime.dvd_mul.mp du).resolve_left d3)
      (Nat.dvd_gcd dv ((prime.dvd_mul.mp dw).resolve_left d3))
    exact prime.not_dvd_one (hp ▸ both)
  have eNorm : 15 * a ^ 2 + 3 * b ^ 2 = 15 * U ^ 2 + 3 * (w : ℤ) ^ 2 := by
    nlinarith only [congrArg (fun z : ℤ ↦ z ^ 2) ha, congrArg (fun z : ℤ ↦ z ^ 2) hb]
  have sqAbs (z : ℤ) : (z.natAbs : ℤ) ^ 2 = z ^ 2 := by
    simpa [pow_two] using Int.natAbs_mul_self z
  have usq : U ^ 2 = (u : ℤ) ^ 2 := by rcases hsign with h | h <;> simp [h]
  have eq : 15 * (a.natAbs : ℤ) ^ 2 + 5 * (v : ℤ) ^ 2 + 3 * (b.natAbs : ℤ) ^ 2 =
      120 * (n : ℤ) + 23 := by
    rw [sqAbs, sqAbs]
    rw [usq] at eNorm
    have q : 15 * (u : ℤ) ^ 2 + 5 * (v : ℤ) ^ 2 + 3 * (w : ℤ) ^ 2 =
        120 * (n : ℤ) + 23 := by exact_mod_cast hq
    linarith [eNorm, q]
  exact ⟨a.natAbs, b.natAbs, by exact_mod_cast eq, hprim, ha₂, hb₁₀⟩

/-- The remaining descent when the heptagonal coordinate is already good. -/
def H1 : Prop :=
  ∀ n u v w : ℕ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23 →
    u.gcd (v.gcd w) = 1 → allOdd u v w → w % 10 = 1 → v % 6 ≠ 1 →
    ¬ (v % 6 = 5 ∧ (u % 4 ≠ v % 4 ∨ 3 * u < v)) →
    ∃ x y z : ℕ, 15 * x ^ 2 + 5 * y ^ 2 + 3 * z ^ 2 = 120 * n + 23 ∧
      x.gcd (y.gcd z) = 1 ∧ rank n x y z < rank n u v w

/-- The remaining descent outside both repair windows for the heptagonal coordinate. -/
def H2 : Prop :=
  ∀ n u v w : ℕ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23 →
    u.gcd (v.gcd w) = 1 → allOdd u v w → w % 10 = 9 →
    ¬ (v % 6 = 5 ∧ (u % 4 ≠ v % 4 ∨ 3 * u < v)) →
    (u + w) % 3 ≠ 0 → (u % 3 = w % 3 → 2 * w ≤ 5 * u) →
    ∃ x y z : ℕ, 15 * x ^ 2 + 5 * y ^ 2 + 3 * z ^ 2 = 120 * n + 23 ∧
      x.gcd (y.gcd z) = 1 ∧ rank n x y z < rank n u v w

theorem main : H1 → H2 → OMA.R_OeisA287616_conjecture_R1_H2_R1.H2 := by
  intro goodW outside
  change ∀ n u v w : ℕ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = 120 * n + 23 →
    u.gcd (v.gcd w) = 1 → allOdd u v w →
    ¬ (v % 6 = 5 ∧ (u % 4 ≠ v % 4 ∨ 3 * u < v)) →
    ¬ (u % 2 = 1 ∧ v % 6 = 1 ∧ w % 10 = 1) →
    ∃ x y z : ℕ, 15 * x ^ 2 + 5 * y ^ 2 + 3 * z ^ 2 = 120 * n + 23 ∧
      x.gcd (y.gcd z) = 1 ∧ rank n x y z < rank n u v w
  intro n u v w hq hp ho hm hf
  have hu := ho.1
  have hv := ho.2.1
  have hw := ho.2.2
  rcases third_residue hq hw with hgood | hbad
  · exact goodW n u v w hq hp ho hgood (fun h ↦ hf ⟨hu, h, hgood⟩) hm
  · by_cases hwin : (u + w) % 3 = 0 ∨ (u % 3 = w % 3 ∧ 5 * u < 2 * w)
    · obtain ⟨x, z, q, prim, hx, hz⟩ := signed_uw_repair hq hp ho hbad hwin
      have hz₂ : z % 2 = 1 := by omega
      refine ⟨x, v, z, q, prim, rank_drop q ?_⟩
      have hh : w % 10 ≠ 1 := by omega
      unfold score
      simp only [hu, hv, hw, hx, hz₂, hh, hz, true_and, and_true, and_false, if_true, if_false]
      split_ifs <;> omega
    · exact outside n u v w hq hp ho hbad hm
        (fun h ↦ hwin (Or.inl h)) (fun he ↦ le_of_not_gt (fun hl ↦ hwin (Or.inr ⟨he, hl⟩)))

end OMA.R_OeisA287616_conjecture_R1_H2_R1_H2_R1
