import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1
import Mathlib.Tactic

/-!
# Column 17 for three remaining exponent classes of A249609

For t = 3240*q+2705, the branch in PR 8363 with q mod 105 in
{7,21,35,77,84,91} has a column-17 witness for 35, 77 and 91.
The two hypotheses retain 7 and 21, and 84, respectively.
The fixed-column division argument comes from PanPapag's PR 5614.
The xor-fold certificates follow the method in PR 8363.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1
open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

private def wt (n : ℕ) := (Nat.digits 2 n).count 1

private lemma half (n : ℕ) : wt n = wt (n/2) + n%2 := by
  have h := count_ones_append (n/2) 1 (n%2) (by simpa using Nat.mod_lt n (by decide : 0 < 2))
  rw [pow_one, Nat.div_add_mod'] at h
  change wt n = wt (n/2) + wt (n%2) at h
  rw [h]
  rcases (show n%2 = 0 ∨ n%2 = 1 by omega) with e|e <;> rw [e] <;> rfl

private lemma xorParity (a b : ℕ) : wt (a ^^^ b) % 2 = (wt a+wt b) % 2 := by
  induction h : a+b using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n = 0
    · have ha : a=0 := by omega
      have hb : b=0 := by omega
      subst_vars; rfl
    have hh := ih (a/2+b/2) (by omega) (a/2) (b/2) rfl
    have ha := half a
    have hb := half b
    have hab := half (a ^^^ b)
    rw [Nat.xor_div_two] at hab
    have hm := Nat.xor_mod_two_eq (m:=a) (n:=b)
    omega

private def foldBits : ℕ → ℕ → ℕ
  | 0, n => wt n % 2
  | j+1, n => let base := 2^(8*2^j); foldBits j ((n/base) ^^^ (n%base))

private theorem fold_exact (j n : ℕ) : foldBits j n = wt n % 2 := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    simp only [foldBits, ih, xorParity]
    have h := count_ones_append (n/2^(8*2^j)) (8*2^j) (n%2^(8*2^j)) (Nat.mod_lt _ (by positivity))
    rw [Nat.div_add_mod'] at h
    exact congrArg (· % 2) h.symm


private def word : List (Bool × ℕ) := [(false, 0), (false, 20922789888000), (true, 70003205961728), (false, 102992244837119), (true, 53659739479424), (false, 48366009233423), (true, 121875921296448), (false, 5374523477959), (true, 139590587071800), (false, 185953177552), (true, 140714431195488), (false, 2185031419), (true, 140737331402896), (false, 8394021), (true, 140737488031648), (false, 8499), (true, 140737488355192), (false, 0)]

set_option maxHeartbeats 4000000 in
private theorem falling17 (x B : ℕ) (hx : 0 < x) (hB : B = 140737488355328) :
    word.foldr (fun s n => (n*x + (if s.1 then x-1 else 0))*B + s.2) 0 =
      (x*B).descFactorial 17 := by
  let low (n c : ℕ) := (n*x+0)*B+c
  let high (n c : ℕ) := (n*x+(x-1))*B+c
  calc
    _ = (low (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 140737488355192) 8499) 140737488031648) 8394021) 140737331402896) 2185031419) 140714431195488) 185953177552) 139590587071800) 5374523477959) 121875921296448) 48366009233423) 53659739479424) 102992244837119) 70003205961728) 20922789888000) 0) := rfl
    _ = _ := by
      dsimp only [low,high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem cert (r : ℕ) (hr : r ∈ ([116105, 252185, 297545, 456305, 592385, 637745] : List ℕ)) :
    (Nat.digits 2 ((2^r).descFactorial 17 / 10854718875)).count 1 % 2 = 0 := by
  change wt _ % 2 = 0
  rw [← fold_exact 21]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem hit (t : ℕ) (ht : 47 ≤ t) (hr : (t-47)%680400+47 ∈ ([116105, 252185, 297545, 456305, 592385, 637745] : List ℕ)) :
    OeisA249609.isEvil ((2^t).choose 17) = true := by
  apply (periodic_column (a:=t) (k:=17) (t:=47) (l:=340200) (d:=10854718875) (z:=15)
    (ds:=word) ht (by decide) (by decide +kernel) (by dsimp only [word]; decide)
    (fun e => by rw [pow_add]; exact falling17 (2^e) (2^47) (by positivity) (by decide))
    (by decide)).2
  exact cert _ hr

def H1 : Prop :=
  ∀ q : ℕ, q % 105 ∈ ([7, 21] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 105 = 84 →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

theorem main : H1 → H2 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1.H1 := by
  intro h1 h2 q hq
  by_cases ha : q % 105 ∈ ([7, 21] : List ℕ)
  · exact h1 q ha
  by_cases hb : q % 105 = 84
  · exact h2 q hb
  refine ⟨17, List.mem_range'_1.mpr ⟨by decide, ?_⟩, hit _ (by omega) ?_⟩
  · have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 3240*q+2705 by omega)
    omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at *
    omega

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1_H1_R1
