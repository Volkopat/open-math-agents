import OMAStatements.S_oeis_a077627
import Mathlib.Tactic

open OMA.S_oeis_a077627

namespace CubicExponentCheck

-- A block advances the ordinary continued fraction by 2^depth digits.
def jump (D h : ℕ) : ℕ → State → State
  | 0, s => step D h s
  | k+1, s => jump D h k (jump D h k s)

lemma state_jump (D start depth : ℕ) :
    state D (start+2^depth) = jump D (Nat.sqrt D) depth (state D start) := by
  induction depth generalizing start with
  | zero => simp [state, jump]
  | succ k ih =>
    rw [show start+2^(k+1)=start+2^k+2^k by ring, ih (start+2^k), ih start, jump]

abbrev D : ℕ := 68630377364882

lemma root_D : Nat.sqrt D = 8284345 := (Nat.eq_sqrt.mpr (by decide)).symm

lemma take_block (start depth : ℕ) (left right : State)
    (hs : state D start = left) (work : jump D 8284345 depth left = right) :
    state D (start+2^depth) = right := by
  rw [state_jump, hs, root_D, work]

-- Each displayed endpoint is independently recomputed by the Lean kernel.
set_option maxHeartbeats 6000000 in
set_option maxRecDepth 32768 in
lemma trace_endpoint : state D 722190 = (8284345,1) := by
  have h0 : state D 0 = (0,1) := rfl
  have h1 : state D 32768 = (8130119,1113337) :=
    take_block 0 15 (0,1) (8130119,1113337) h0 (by decide +kernel)
  have h2 : state D 65536 = (5239812,6942601) :=
    take_block 32768 15 (8130119,1113337) (5239812,6942601) h1 (by decide +kernel)
  have h3 : state D 98304 = (8237586,7395553) :=
    take_block 65536 15 (5239812,6942601) (8237586,7395553) h2 (by decide +kernel)
  have h4 : state D 131072 = (8191607,1018721) :=
    take_block 98304 15 (8237586,7395553) (8191607,1018721) h3 (by decide +kernel)
  have h5 : state D 163840 = (3981738,5393017) :=
    take_block 131072 15 (8191607,1018721) (3981738,5393017) h4 (by decide +kernel)
  have h6 : state D 196608 = (6818997,1559809) :=
    take_block 163840 15 (3981738,5393017) (6818997,1559809) h5 (by decide +kernel)
  have h7 : state D 229376 = (7344177,2750407) :=
    take_block 196608 15 (6818997,1559809) (7344177,2750407) h6 (by decide +kernel)
  have h8 : state D 262144 = (7486306,7869182) :=
    take_block 229376 15 (7344177,2750407) (7486306,7869182) h7 (by decide +kernel)
  have h9 : state D 294912 = (8069178,697207) :=
    take_block 262144 15 (7486306,7869182) (8069178,697207) h8 (by decide +kernel)
  have h10 : state D 327680 = (7876282,4819714) :=
    take_block 294912 15 (8069178,697207) (7876282,4819714) h9 (by decide +kernel)
  have h11 : state D 360448 = (7510892,1166329) :=
    take_block 327680 15 (7876282,4819714) (7510892,1166329) h10 (by decide +kernel)
  have h12 : state D 393216 = (5531710,4253102) :=
    take_block 360448 15 (7510892,1166329) (5531710,4253102) h11 (by decide +kernel)
  have h13 : state D 425984 = (6114407,12059719) :=
    take_block 393216 15 (5531710,4253102) (6114407,12059719) h12 (by decide +kernel)
  have h14 : state D 458752 = (780029,8968057) :=
    take_block 425984 15 (6114407,12059719) (780029,8968057) h13 (by decide +kernel)
  have h15 : state D 491520 = (4492381,8612023) :=
    take_block 458752 15 (780029,8968057) (4492381,8612023) h14 (by decide +kernel)
  have h16 : state D 524288 = (1526740,9063778) :=
    take_block 491520 15 (4492381,8612023) (1526740,9063778) h15 (by decide +kernel)
  have h17 : state D 557056 = (4207870,10609106) :=
    take_block 524288 15 (1526740,9063778) (4207870,10609106) h16 (by decide +kernel)
  have h18 : state D 589824 = (7097914,3700354) :=
    take_block 557056 15 (4207870,10609106) (7097914,3700354) h17 (by decide +kernel)
  have h19 : state D 622592 = (4283666,4851854) :=
    take_block 589824 15 (7097914,3700354) (4283666,4851854) h18 (by decide +kernel)
  have h20 : state D 655360 = (6039594,7614127) :=
    take_block 622592 15 (4283666,4851854) (6039594,7614127) h19 (by decide +kernel)
  have h21 : state D 688128 = (5711112,8616082) :=
    take_block 655360 15 (6039594,7614127) (5711112,8616082) h20 (by decide +kernel)
  have h22 : state D 720896 = (5426886,6165074) :=
    take_block 688128 15 (5711112,8616082) (5426886,6165074) h21 (by decide +kernel)
  have h23 : state D 721920 = (5251472,11677106) :=
    take_block 720896 10 (5426886,6165074) (5251472,11677106) h22 (by decide +kernel)
  have h24 : state D 722176 = (5967838,4491679) :=
    take_block 721920 8 (5251472,11677106) (5967838,4491679) h23 (by decide +kernel)
  have h25 : state D 722184 = (5975062,2724802) :=
    take_block 722176 3 (5967838,4491679) (5975062,2724802) h24 (by decide +kernel)
  have h26 : state D 722188 = (7360280,2133358) :=
    take_block 722184 2 (5975062,2724802) (7360280,2133358) h25 (by decide +kernel)
  have h27 : state D 722190 = (8284345,1) :=
    take_block 722188 1 (7360280,2133358) (8284345,1) h26 (by decide +kernel)
  exact h27

lemma digit_at_state (N j m d : ℕ) (hs : state N j = (m,d)) :
    partialQuotient N j = (((Nat.sqrt N+m)/d:ℕ):ℤ) := by
  simp only [partialQuotient, hs]

lemma table_digit : (16568690 : ℤ) ∈ periodTerms (3^29-1) := by
  rw [show (3:ℕ)^29-1=D by decide]
  have digit := digit_at_state D 722190 8284345 1 trace_endpoint
  rw [root_D] at digit
  exact ⟨722189, digit⟩

lemma ceiling_at_29 : ⌈comparison 29⌉ = 16568689 := by
  have lo : (8284345:ℝ) < Real.sqrt ((3:ℝ)^29) :=
    Real.lt_sqrt_of_sq_lt (by norm_num)
  have hi : Real.sqrt ((3:ℝ)^29) ≤ 16568691/2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [Int.ceil_eq_iff]
  change (16568689:ℝ)-1 < 2*(Real.sqrt ((3:ℝ)^29)-1) ∧
    2*(Real.sqrt ((3:ℝ)^29)-1) ≤ 16568689
  constructor
  · linarith only [lo]
  · calc
      2*(Real.sqrt ((3:ℝ)^29)-1) ≤ 2*((16568691:ℝ)/2-1) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hi 1) (by norm_num)
      _ = 16568689 := by norm_num

end CubicExponentCheck

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a077627.main) := by
  intro claim
  obtain ⟨z, hg, _, _, _, plain⟩ := claim 29 (by decide)
  have noPower : ¬ ∃ k : ℕ, 29=3^(k+1) := by
    rintro ⟨k, hk⟩
    have hd : 3 ∣ (29:ℕ) := hk ▸ dvd_pow_self _ (by omega)
    exact (by decide : ¬3 ∣ (29:ℕ)) hd
  have hmax := hg.2 CubicExponentCheck.table_digit
  rw [plain noPower, CubicExponentCheck.ceiling_at_29] at hmax
  omega
