import OMAReductions.R_OeisA72200_conjecture_R1

/-! Count decimal sixes in factorials through 10000. Below 240, the window
contains the whole factorial. Above that cutoff, a window of 520 digits
contains at least 25 sixes. The offset skips most trailing zeroes.
The table at tripleCount stores the six-count of each three-digit block
in two bits. smallCounts verifies every entry. -/

namespace OMA.FactorialSixes

def sixes (n : ℕ) : ℕ := (Nat.digits 10 n).count 6

def unitCount (n : ℕ) : ℕ := if n % 10 = 6 then 1 else 0

theorem splitOne (n : ℕ) : sixes n = unitCount n + sixes (n / 10) := by
  by_cases h : n = 0
  · simp [h, sixes, unitCount]
  · unfold sixes
    rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 10) h, List.count_cons]
    simp [unitCount, Nat.add_comm]

theorem splitAt (n width : ℕ) :
    sixes n = sixes (n % 10 ^ width) + sixes (n / 10 ^ width) := by
  induction width generalizing n with
  | zero => simp [sixes, Nat.mod_one]
  | succ k ih =>
    rw [pow_succ', splitOne n, splitOne (n % (10 * 10 ^ k)), Nat.mod_mul_right_div_self,
      ← Nat.div_div_eq_div_mul, ih (n / 10), Nat.add_assoc]
    simp [unitCount]

def countTail : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t + 1, x => unitCount x + countTail t (x / 10)

theorem tailEq (t x : ℕ) : countTail t x + sixes (x / 10 ^ t) = sixes x := by
  induction t generalizing x with
  | zero => simp [countTail]
  | succ t ih =>
    rw [countTail, pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_assoc, ih, ← splitOne]


def tripleCount (x : ℕ) : ℕ := (448488980553927652226111531763054703062583866095033660223133427516941289066723240677560684810621339380365827735046607350347393903816992819077938714319496893483002913328707031246666680443970381488671953831530969435088753032134107328560842522810094265820070881673750378148826356315588199794479265969510104350921607470091725985246473827077969061003112927765856843507238078750228653829756284430192653233452007107276768182794175731979791171795108612752132220321419521032517091619019451083838047316768357912185768294366045381552380227476311059995798858221987898937699443334832151606837210908326024135577600 >>> (2*x)) % 4

set_option maxRecDepth 12000 in
theorem smallCounts (i : Fin 1000) : tripleCount i = countTail 3 i := by
  revert i
  decide +kernel

theorem splitThree (x : ℕ) : tripleCount (x % 1000) + sixes (x / 1000) = sixes x := by
  have t := tailEq 3 (x % 1000)
  change countTail 3 (x % 1000) + sixes (x % 1000 / 1000) = _ at t
  rw [Nat.div_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 1000))] at t
  have z : sixes 0 = 0 := rfl
  rw [z, Nat.add_zero] at t
  rw [smallCounts ⟨x % 1000, Nat.mod_lt _ (by decide)⟩, t]
  exact (splitAt x 3).symm

def enough : ℕ → ℕ → ℕ → Bool
  | 0, _, need => need == 0
  | fuel+1, x, need => need == 0 || enough fuel (x / 1000) (need - tripleCount (x % 1000))

theorem enoughSound (fuel x need : ℕ) (h : enough fuel x need = true) : need ≤ sixes x := by
  induction fuel generalizing x need with
  | zero =>
    have z : need = 0 := by simpa [enough] using h
    omega
  | succ fuel ih =>
    change (_ || _) = true at h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · have : need = 0 := beq_iff_eq.mp h
      omega
    · have tail := ih _ _ h
      have both := splitThree x
      omega

def checkOne (k f : ℕ) : Bool :=
  if k < 240 then
    decide (countTail 520 f ≠ 24)
  else
    enough 174 (f / 10 ^ (k / 4 - 6) % 10 ^ 520) 25

set_option maxRecDepth 2000 in
theorem oneSound {k f : ℕ} (valid : checkOne k f = true) (hf : f = k.factorial) :
    sixes f ≠ 24 := by
  unfold checkOne at valid
  split at valid
  next hk =>
    have hd : f < 10 ^ 520 := by
      rw [hf]
      exact (Nat.factorial_le (show k ≤ 240 by omega)).trans_lt (by decide +kernel)
    have c := tailEq 520 f
    rw [Nat.div_eq_of_lt hd] at c
    simp [sixes] at c
    simpa only [decide_eq_true_eq, c, sixes] using valid
  next =>
    have a := enoughSound _ _ _ valid
    have b := splitAt (f / 10 ^ (k / 4 - 6)) 520
    have c := splitAt f (k / 4 - 6)
    omega

def run : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | len + 1, k, f => checkOne k f && run len (k+1) (f*(k+1))

theorem runSound (len k f : ℕ) (hf : f = k.factorial) (h : run len k f = true)
    (n : ℕ) (lo : k ≤ n) (hi : n < k+len) : sixes n.factorial ≠ 24 := by
  induction len generalizing k f with
  | zero => omega
  | succ len ih =>
    obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
    by_cases eq : n = k
    · subst n
      exact hf ▸ oneSound a hf
    · apply ih (k+1) (f*(k+1))
      · rw [hf, Nat.factorial_succ, Nat.mul_comm]
      · exact b
      · omega
      · omega


def goodRange (a b : ℕ) : Prop := ∀ n, a ≤ n → n < b → sixes n.factorial ≠ 24

theorem joinRanges {a b c : ℕ} (lo : goodRange a b) (hi : goodRange b c) :
    goodRange a c := by
  intro n h₁ h₂
  by_cases h : n < b
  · exact lo n h₁ h
  · exact hi n (by omega) h₂

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band0 : goodRange 0 128 :=
  runSound 128 0 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band128 : goodRange 128 256 :=
  runSound 128 128 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band256 : goodRange 256 384 :=
  runSound 128 256 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band384 : goodRange 384 512 :=
  runSound 128 384 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band512 : goodRange 512 640 :=
  runSound 128 512 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band640 : goodRange 640 768 :=
  runSound 128 640 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band768 : goodRange 768 896 :=
  runSound 128 768 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band896 : goodRange 896 1024 :=
  runSound 128 896 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band1024 : goodRange 1024 1152 :=
  runSound 128 1024 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band1152 : goodRange 1152 1280 :=
  runSound 128 1152 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band1280 : goodRange 1280 1408 :=
  runSound 128 1280 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band1408 : goodRange 1408 1536 :=
  runSound 128 1408 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band1536 : goodRange 1536 1664 :=
  runSound 128 1536 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band1664 : goodRange 1664 1792 :=
  runSound 128 1664 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band1792 : goodRange 1792 1920 :=
  runSound 128 1792 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band1920 : goodRange 1920 2048 :=
  runSound 128 1920 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band2048 : goodRange 2048 2176 :=
  runSound 128 2048 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band2176 : goodRange 2176 2304 :=
  runSound 128 2176 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band2304 : goodRange 2304 2432 :=
  runSound 128 2304 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band2432 : goodRange 2432 2560 :=
  runSound 128 2432 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band2560 : goodRange 2560 2688 :=
  runSound 128 2560 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band2688 : goodRange 2688 2816 :=
  runSound 128 2688 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band2816 : goodRange 2816 2944 :=
  runSound 128 2816 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band2944 : goodRange 2944 3072 :=
  runSound 128 2944 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band3072 : goodRange 3072 3200 :=
  runSound 128 3072 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band3200 : goodRange 3200 3328 :=
  runSound 128 3200 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band3328 : goodRange 3328 3456 :=
  runSound 128 3328 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band3456 : goodRange 3456 3584 :=
  runSound 128 3456 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band3584 : goodRange 3584 3712 :=
  runSound 128 3584 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band3712 : goodRange 3712 3840 :=
  runSound 128 3712 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band3840 : goodRange 3840 3968 :=
  runSound 128 3840 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band3968 : goodRange 3968 4096 :=
  runSound 128 3968 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band4096 : goodRange 4096 4224 :=
  runSound 128 4096 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band4224 : goodRange 4224 4352 :=
  runSound 128 4224 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band4352 : goodRange 4352 4480 :=
  runSound 128 4352 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band4480 : goodRange 4480 4608 :=
  runSound 128 4480 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band4608 : goodRange 4608 4736 :=
  runSound 128 4608 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band4736 : goodRange 4736 4864 :=
  runSound 128 4736 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band4864 : goodRange 4864 4992 :=
  runSound 128 4864 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band4992 : goodRange 4992 5120 :=
  runSound 128 4992 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band5120 : goodRange 5120 5248 :=
  runSound 128 5120 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band5248 : goodRange 5248 5376 :=
  runSound 128 5248 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band5376 : goodRange 5376 5504 :=
  runSound 128 5376 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band5504 : goodRange 5504 5632 :=
  runSound 128 5504 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band5632 : goodRange 5632 5760 :=
  runSound 128 5632 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band5760 : goodRange 5760 5888 :=
  runSound 128 5760 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band5888 : goodRange 5888 6016 :=
  runSound 128 5888 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band6016 : goodRange 6016 6144 :=
  runSound 128 6016 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band6144 : goodRange 6144 6272 :=
  runSound 128 6144 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band6272 : goodRange 6272 6400 :=
  runSound 128 6272 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band6400 : goodRange 6400 6528 :=
  runSound 128 6400 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band6528 : goodRange 6528 6656 :=
  runSound 128 6528 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band6656 : goodRange 6656 6784 :=
  runSound 128 6656 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band6784 : goodRange 6784 6912 :=
  runSound 128 6784 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band6912 : goodRange 6912 7040 :=
  runSound 128 6912 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band7040 : goodRange 7040 7168 :=
  runSound 128 7040 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band7168 : goodRange 7168 7296 :=
  runSound 128 7168 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band7296 : goodRange 7296 7424 :=
  runSound 128 7296 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band7424 : goodRange 7424 7552 :=
  runSound 128 7424 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band7552 : goodRange 7552 7680 :=
  runSound 128 7552 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band7680 : goodRange 7680 7808 :=
  runSound 128 7680 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band7808 : goodRange 7808 7936 :=
  runSound 128 7808 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band7936 : goodRange 7936 8064 :=
  runSound 128 7936 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band8064 : goodRange 8064 8192 :=
  runSound 128 8064 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band8192 : goodRange 8192 8320 :=
  runSound 128 8192 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band8320 : goodRange 8320 8448 :=
  runSound 128 8320 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band8448 : goodRange 8448 8576 :=
  runSound 128 8448 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band8576 : goodRange 8576 8704 :=
  runSound 128 8576 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band8704 : goodRange 8704 8832 :=
  runSound 128 8704 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band8832 : goodRange 8832 8960 :=
  runSound 128 8832 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band8960 : goodRange 8960 9088 :=
  runSound 128 8960 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band9088 : goodRange 9088 9216 :=
  runSound 128 9088 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band9216 : goodRange 9216 9344 :=
  runSound 128 9216 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band9344 : goodRange 9344 9472 :=
  runSound 128 9344 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band9472 : goodRange 9472 9600 :=
  runSound 128 9472 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band9600 : goodRange 9600 9728 :=
  runSound 128 9600 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band9728 : goodRange 9728 9856 :=
  runSound 128 9728 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band9856 : goodRange 9856 9984 :=
  runSound 128 9856 _ rfl (by decide +kernel)

set_option maxRecDepth 24000 in
set_option maxHeartbeats 16000000 in
theorem band9984 : goodRange 9984 10001 :=
  runSound 17 9984 _ rfl (by decide +kernel)

theorem allChecked : goodRange 0 10001 :=
  (joinRanges (joinRanges (joinRanges (joinRanges (joinRanges (joinRanges (joinRanges band0 band128) (joinRanges band256 band384)) (joinRanges (joinRanges band512 band640) (joinRanges band768 band896))) (joinRanges (joinRanges (joinRanges band1024 band1152) (joinRanges band1280 band1408)) (joinRanges (joinRanges band1536 band1664) (joinRanges band1792 band1920)))) (joinRanges (joinRanges (joinRanges (joinRanges band2048 band2176) (joinRanges band2304 band2432)) (joinRanges (joinRanges band2560 band2688) (joinRanges band2816 band2944))) (joinRanges (joinRanges (joinRanges band3072 band3200) (joinRanges band3328 band3456)) (joinRanges (joinRanges band3584 band3712) (joinRanges band3840 band3968))))) (joinRanges (joinRanges (joinRanges (joinRanges (joinRanges band4096 band4224) (joinRanges band4352 band4480)) (joinRanges (joinRanges band4608 band4736) (joinRanges band4864 band4992))) (joinRanges (joinRanges (joinRanges band5120 band5248) (joinRanges band5376 band5504)) (joinRanges (joinRanges band5632 band5760) (joinRanges band5888 band6016)))) (joinRanges (joinRanges (joinRanges (joinRanges band6144 band6272) (joinRanges band6400 band6528)) (joinRanges (joinRanges band6656 band6784) (joinRanges band6912 band7040))) (joinRanges (joinRanges (joinRanges band7168 band7296) (joinRanges band7424 band7552)) (joinRanges (joinRanges band7680 band7808) (joinRanges band7936 band8064)))))) (joinRanges (joinRanges (joinRanges (joinRanges band8192 band8320) (joinRanges band8448 band8576)) (joinRanges (joinRanges band8704 band8832) (joinRanges band8960 band9088))) (joinRanges (joinRanges (joinRanges band9216 band9344) (joinRanges band9472 band9600)) (joinRanges (joinRanges band9728 band9856) band9984))))

end OMA.FactorialSixes

theorem OMA.solution : OMA.R_OeisA72200_conjecture_R1.H1 := by
  intro k hk
  exact OMA.FactorialSixes.allChecked k (Nat.zero_le _) (by omega)
