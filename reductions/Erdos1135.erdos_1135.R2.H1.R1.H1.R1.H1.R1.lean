import OMAReductions.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1

-- Reduction Erdos1135.erdos_1135.R2.H1.R1.H1.R1.H1.R1 of step Erdos1135.erdos_1135.R2.H1.R1.H1.R1.H1
-- Credit: @Ciphore

/-! The `3 (mod 8)` accelerated-Collatz core is refined to modulo `1024`.
A kernel-checked finite certificate discharges 115 of the 128 residue classes in that congruence
class within ten accelerated steps. The thirteen remaining classes are grouped by their previous
modulo-`256` class so the four cores remain independent. -/

namespace OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1_H1_R1

open Function

/-- Depth-ten resistant `3 (mod 8)` residue classes modulo `1024`, group 1. -/
def H1 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 8 = 3 → n % 1024 ∈ ([27, 283, 539, 795] : List ℕ) → ∃ k : ℕ, T^[k] n < n

/-- Depth-ten resistant `3 (mod 8)` residue classes modulo `1024`, group 2. -/
def H2 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 8 = 3 → n % 1024 ∈ ([91, 603, 859] : List ℕ) → ∃ k : ℕ, T^[k] n < n

/-- Depth-ten resistant `3 (mod 8)` residue classes modulo `1024`, group 3. -/
def H3 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 8 = 3 → n % 1024 ∈ ([155, 411, 667] : List ℕ) → ∃ k : ℕ, T^[k] n < n

/-- Depth-ten resistant `3 (mod 8)` residue classes modulo `1024`, group 4. -/
def H4 : Prop :=
  let T := fun n : ℕ => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2
  ∀ n : ℕ, 2048 < n → n % 8 = 3 → n % 1024 ∈ ([251, 763, 1019] : List ℕ) → ∃ k : ℕ, T^[k] n < n

/-- The quotient in an entire residue class enters each accelerated iterate affinely. -/
theorem residue_affine (T : ℕ → ℕ)
    (hT : ∀ n, T n = if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) (j r : ℕ) :
    ∃ a : ℕ, ∀ x : ℕ, T^[j] (2 ^ j * x + r) = a * x + T^[j] r := by
  have one_step (x b : ℕ) : T (2 * x + b) = (if b % 2 = 0 then 1 else 3) * x + T b := by
    simp only [hT]
    split_ifs <;> omega
  induction j generalizing r with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨a, ha⟩ := ih (T r)
    let b : ℕ := if r % 2 = 0 then 1 else 3
    refine ⟨a * b, fun x => ?_⟩
    rw [iterate_succ_apply, iterate_succ_apply T j r]
    rw [show 2 ^ (j + 1) * x + r = 2 * (2 ^ j * x) + r by ring, one_step]
    change T^[j] (b * (2 ^ j * x) + T r) = _
    rw [show b * (2 ^ j * x) = 2 ^ j * (b * x) by ring, ha, Nat.mul_assoc]

lemma not_mem_four_append {x : ℕ} {a b c d : List ℕ}
    (ha : x ∉ a) (hb : x ∉ b) (hc : x ∉ c) (hd : x ∉ d) :
    x ∉ a ++ b ++ c ++ d := by
  intro h
  simp only [List.mem_append] at h
  tauto

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
theorem certificate1024 (T : ℕ → ℕ)
    (hT : T = fun n => if n % 2 = 0 then n / 2 else (3 * n + 1) / 2) :
    ∀ r : Fin 1024, (r.val + 2) % 8 = 3 → (r.val + 2) % 1024 ∉ ([27, 283, 539, 795] : List ℕ) ++ ([91, 603, 859] : List ℕ) ++ ([155, 411, 667] : List ℕ) ++ ([251, 763, 1019] : List ℕ) →
      ∃ j : Fin 11, T^[j.val] (r.val + 2) < r.val + 2 ∧
        T^[j.val] (1024 + (r.val + 2)) ≤ 1024 + T^[j.val] (r.val + 2) := by
  subst T
  decide +kernel

theorem forward_descent1024 {n : ℕ} (hn : 2048 < n) (hmod : n % 8 = 3)
    (hres : n % 1024 ∉ ([27, 283, 539, 795] : List ℕ) ++ ([91, 603, 859] : List ℕ) ++ ([155, 411, 667] : List ℕ) ++ ([251, 763, 1019] : List ℕ)) :
    ∃ k, (fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2)^[k] n < n := by
  let T := fun v : ℕ => if v % 2 = 0 then v / 2 else (3 * v + 1) / 2
  change ∃ k, T^[k] n < n
  let r : Fin 1024 := ⟨(n - 2) % 1024, Nat.mod_lt _ (by decide)⟩
  let b := r.val + 2
  let q := (n - 2) / 1024
  have hnq : n = 1024 * q + b := by dsimp [q, b, r]; omega
  have hb : b % 1024 = n % 1024 := by omega
  have hb8 : b % 8 = 3 := by
    have hcongr : (b % 1024) % 8 = (n % 1024) % 8 := by rw [hb]
    rw [Nat.mod_mod_of_dvd b (by decide : 8 ∣ 1024),
        Nat.mod_mod_of_dvd n (by decide : 8 ∣ 1024)] at hcongr
    exact hcongr.trans hmod
  obtain ⟨j, hdrop, hslope⟩ := certificate1024 T rfl r hb8 (by simpa only [← hb] using hres)
  change T^[j.val] b < b at hdrop
  change T^[j.val] (1024 + b) ≤ 1024 + T^[j.val] b at hslope
  let d := 2 ^ (10 - j.val)
  have hj : j.val ≤ 10 := by omega
  have hd : 2 ^ j.val * d = 1024 := by
    dsimp [d]
    rw [← pow_add, show j.val + (10 - j.val) = 10 by omega]
    decide
  obtain ⟨a, ha⟩ := residue_affine T (fun _ => rfl) j.val b
  have ha' := ha d
  rw [hd] at ha'
  have had : a * d ≤ 1024 := by omega
  have hcalc : T^[j.val] n = a * d * q + T^[j.val] b := by
    calc T^[j.val] n = T^[j.val] (2 ^ j.val * (d * q) + b) := by rw [← Nat.mul_assoc, hd, ← hnq]
         _ = _ := by rw [ha, Nat.mul_assoc]
  exact ⟨j.val, by rw [hcalc]; have := Nat.mul_le_mul_right q had; omega⟩

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1.H1 := by
  intro hA hB hC hD n hn hmod
  by_cases hA' : n % 1024 ∈ ([27, 283, 539, 795] : List ℕ)
  · exact hA n hn hmod hA'
  by_cases hB' : n % 1024 ∈ ([91, 603, 859] : List ℕ)
  · exact hB n hn hmod hB'
  by_cases hC' : n % 1024 ∈ ([155, 411, 667] : List ℕ)
  · exact hC n hn hmod hC'
  by_cases hD' : n % 1024 ∈ ([251, 763, 1019] : List ℕ)
  · exact hD n hn hmod hD'
  apply forward_descent1024 hn hmod
  exact not_mem_four_append hA' hB' hC' hD'

end OMA.R_Erdos1135_erdos_1135_R2_H1_R1_H1_R1_H1_R1
