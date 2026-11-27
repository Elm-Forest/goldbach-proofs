import Conjectures.Goldbach.InnerFloorFixedPowerBands

/-! Use global n-based smoothing and truncation parameters on all
integer dyadic blocks, avoiding an extra local log-scale parameter.
The endpoint exponent a and window exponent c have fixed slack.
No zero-free theorem is assumed or asserted in this file. -/
open Filter Finset
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem fixedBandGlobalExponents (j : ℕ) (hj : j < 10) :
    let a := fixedBandUpperExp j
    let c := fixedBandWindowExp j
    1/50 ≤ a ∧ a ≤ 1/5 ∧ 4/5+1/100 ≤ c ∧
    2*a+7/12 ≤ c-1/150 ∧
    a+3/2 ≤ 2*c-1/10 ∧
    a+2/3 ≤ c-1/10 ∧
    a-1/6 ≤ c-1/10 ∧
    3*a-1/6 ≤ c-1/10 ∧
    a+1/2 ≤ c-1/4 := by
  dsimp only
  interval_cases j <;> norm_num [fixedBandUpperExp,fixedBandWindowExp,
    fixedBandLowerExp,min_def]

private theorem cutoff_log_square (n : ℕ) (hn : 2 ≤ n) :
    (innerCutoff n:ℝ) ≤ 16*(Real.log (n:ℝ))^2 := by
  have hp : (2:ℝ)^Nat.log 2 (n+2) ≤ ((n+2:ℕ):ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n+2≠0)
  have hraw := Real.log_le_log (by positivity) hp
  have hin : ((n+2:ℕ):ℝ) ≤ (n:ℝ)^2 := by
    push_cast
    nlinarith only [(show (2:ℝ) ≤ n by exact_mod_cast hn),sq_nonneg ((n:ℝ)-2)]
  have hlog' := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog'
  have hl2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 (n+2)))
  have hL : (Nat.log 2 (n+2):ℝ) ≤ 4*Real.log n := by
    push_cast at hraw hlog'
    linarith only [hraw,hlog',hm]
  unfold innerCutoff GoldbachGRHBudget.narrow
  push_cast
  calc
    _ ≤ (4*Real.log n)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
    _ = _ := by ring

theorem eventualFixedBandPowerEndpoints : ∀ᶠ n : ℕ in atTop,
    ∀ j < 10,
      1 ≤ fixedBandEnd n (j+1) ∧
      (fixedBandEnd n (j+1):ℝ) ≤ (n:ℝ)^fixedBandUpperExp j ∧
      (n:ℝ)^fixedBandWindowExp j ≤ 2*(fixedBandWindow n j:ℝ) := by
  filter_upwards [eventualInnerGeometry,eventualFixedBandWindows,
    GoldbachGRHBudget.eventually_log_pow_le 2 (1/100) (1/16) (by norm_num) (by norm_num)]
    with n hg hw hlog
  intro j hj
  obtain ⟨hn,hQ,hQA,hAB,huH,hsep⟩ := hg
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hQsmall : (innerCutoff n:ℝ) ≤ (n:ℝ)^(1/100:ℝ) :=
    (cutoff_log_square n hn).trans (by linarith only [hlog])
  have ha : (1/100:ℝ) ≤ fixedBandUpperExp j := by
    unfold fixedBandUpperExp
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) j]
  have hQpow := hQsmall.trans (Real.rpow_le_rpow_of_exponent_le hnR ha)
  have hfl : (⌊(n:ℝ)^fixedBandLowerExp (j+1)⌋₊:ℝ) ≤
      (n:ℝ)^fixedBandUpperExp j :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hA : 1 ≤ fixedBandEnd n (j+1) := hQ.trans (le_max_left _ _)
  have hh1 : (1:ℝ) ≤ fixedBandWindow n j :=
    (Real.one_le_rpow hnR (by norm_num : (0:ℝ) ≤ 4/5)).trans (hw j hj).1
  have hf := Nat.lt_floor_add_one ((n:ℝ)^fixedBandWindowExp j)
  change (n:ℝ)^fixedBandWindowExp j < (fixedBandWindow n j:ℝ)+1 at hf
  refine ⟨hA,?_,by linarith⟩
  unfold fixedBandEnd
  push_cast
  exact max_le hQpow hfl

def fixedTruncationIndex (n : ℕ) : ℕ := Nat.log 2 ⌊(n:ℝ)^(3/2:ℝ)⌋₊

theorem fixedTruncation_bounds (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)^(3/2:ℝ) ≤ (2:ℝ)^(fixedTruncationIndex n+1) ∧
    (2:ℝ)^(fixedTruncationIndex n+1) ≤ 2*(n:ℝ)^(3/2:ℝ) := by
  let R := (n:ℝ)^(3/2:ℝ)
  let m := ⌊R⌋₊
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hm : 1 ≤ m := Nat.le_floor (Real.one_le_rpow hnR (by norm_num))
  have hupper : (2:ℕ)^(Nat.log 2 m) ≤ m :=
    Nat.pow_log_le_self 2 (by omega)
  have hlower := Nat.lt_pow_succ_log_self (by decide : 1 < 2) m
  have hf := Nat.lt_floor_add_one R
  have hF : (m:ℝ) ≤ R := Nat.floor_le (by dsimp [R]; positivity)
  have hu : (2:ℝ)^(Nat.log 2 m) ≤ (m:ℝ) := by exact_mod_cast hupper
  have hl : (m:ℝ)+1 ≤ (2:ℝ)^(Nat.log 2 m+1) := by
    exact_mod_cast (show m+1 ≤ 2^(Nat.log 2 m+1) by omega)
  change R ≤ (2:ℝ)^(Nat.log 2 m+1) ∧ (2:ℝ)^(Nat.log 2 m+1) ≤ 2*R
  constructor
  · exact hf.le.trans hl
  · rw [pow_succ]
    nlinarith only [hu,hF]

theorem fixedTruncation_logBound (n : ℕ) (hn : 2 ≤ n) :
    ((fixedTruncationIndex n+1:ℕ):ℝ) ≤ 5*Real.log (n:ℝ) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnP : (0:ℝ) < n := by linarith
  have hlog := Real.log_le_log (by positivity) (fixedTruncation_bounds n (by omega)).2
  rw [Real.log_pow,Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hnP _).ne',
    Real.log_rpow hnP] at hlog
  have hL2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL := Real.log_le_log (by norm_num : (0:ℝ) < 2) hnR
  have H := mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg (fixedTruncationIndex n+1))
  nlinarith only [hlog,H,hL]

end
end InnerFloorResearch
