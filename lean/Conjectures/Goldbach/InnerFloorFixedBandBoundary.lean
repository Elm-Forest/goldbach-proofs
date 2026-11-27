import Conjectures.Goldbach.InnerFloorFixedPowerBands
import Conjectures.Goldbach.InnerFloorDyadicBandAssembly

/-! Independent fixed-band partition and clipped boundary power budget.
This file does not assume a zero-free strip or assert the frozen theorem. -/
open Filter Finset InnerFloorLinearTotient
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem mediumCellEnergy_fixed_sum (n : ℕ) (u : ℝ)
    (hn : 1 ≤ n) (hQ : 1 ≤ innerCutoff n)
    (hQA : innerCutoff n ≤ middleCutoff n) :
    mediumCellEnergy n (innerCutoff n) (middleCutoff n) u =
      ∑ j∈range 10,mediumCellEnergy n (fixedBandEnd n j)
        (fixedBandEnd n (j+1)) u := by
  have h0 := fixedBandEnd_zero n hQ
  have h10 := fixedBandEnd_ten n hQA
  have hp (k : ℕ) : mediumCellEnergy n (innerCutoff n) (fixedBandEnd n k) u =
      ∑ j∈range k,mediumCellEnergy n (fixedBandEnd n j)
        (fixedBandEnd n (j+1)) u := by
    induction k with
    | zero =>
      rw [h0]
      simp [mediumCellEnergy,sum_mediumIndices]
    | succ k ih =>
      have hq : innerCutoff n ≤ fixedBandEnd n k := by
        rw [← h0]
        exact fixedBandEnd_mono n hn (Nat.zero_le _)
      rw [mediumCellEnergy_split n (innerCutoff n) (fixedBandEnd n k)
        (fixedBandEnd n (k+1)) u hq
        (fixedBandEnd_mono n hn (Nat.le_succ _)),ih,sum_range_succ]
  simpa only [h10] using hp 10

theorem mediumCellEnergy_of_fixed_bounds (n : ℕ) (u M : ℝ)
    (hn : 1 ≤ n) (hQ : 1 ≤ innerCutoff n)
    (hQA : innerCutoff n ≤ middleCutoff n)
    (hb : ∀ j < 10,mediumCellEnergy n (fixedBandEnd n j)
      (fixedBandEnd n (j+1)) u ≤ M) :
    mediumCellEnergy n (innerCutoff n) (middleCutoff n) u ≤ 10*M := by
  rw [mediumCellEnergy_fixed_sum n u hn hQ hQA]
  calc
    _ ≤ ∑ _j∈range 10,M := sum_le_sum fun j hj => hb j (mem_range.mp hj)
    _ = _ := by simp [nsmul_eq_mul]

/-- The actual clipped-boundary term in the band estimate divided
by h². If A² ≤ h and log(A) ≤ log(n+2), its growth is h log²(n+2). -/
theorem fixedBand_boundary_scalar (A n h : ℕ)
    (hA : 1 ≤ A) (hh : 0 < h) (hA2 : (A:ℝ)^2 ≤ (h:ℝ))
    (hlog : Real.log (A:ℝ) ≤ Real.log ((n+2:ℕ):ℝ)) :
    4*((2*h+2*h:ℕ):ℝ)*boundaryWindowBudget A n h/(h:ℝ)^2 ≤ 16*(h:ℝ)*(256*(Real.log ((n+2:ℕ):ℝ))^2+
        2*(weightConstant*(1+Real.log ((n+2:ℕ):ℝ)))^2) := by
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hlogA : 0 ≤ Real.log (A:ℝ) := Real.log_nonneg (by exact_mod_cast hA)
  have hlogN : 0 ≤ Real.log ((n+2:ℕ):ℝ) := hlogA.trans hlog
  have hW := weightConstant_nonneg
  have hpow : (weightConstant*(1+Real.log (A:ℝ)))^2 ≤ (weightConstant*(1+Real.log ((n+2:ℕ):ℝ)))^2 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hW
  have he : boundaryWindowBudget A n h ≤ (h:ℝ)^2*(256*(Real.log ((n+2:ℕ):ℝ))^2+
        2*(weightConstant*(1+Real.log ((n+2:ℕ):ℝ)))^2) := by
    unfold boundaryWindowBudget
    calc
      _ ≤ 128*((h:ℝ)+(h:ℝ))*(h:ℝ)*(Real.log ((n+2:ℕ):ℝ))^2+
          2*(h:ℝ)^2*(weightConstant*(1+Real.log ((n+2:ℕ):ℝ)))^2 := by
        gcongr
      _ = _ := by ring
  apply (div_le_iff₀ (sq_pos_of_pos hhR)).2
  push_cast
  calc
    _ ≤ 4*(2*(h:ℝ)+2*(h:ℝ))*((h:ℝ)^2*
        (256*(Real.log ((n+2:ℕ):ℝ))^2+
        2*(weightConstant*(1+Real.log ((n+2:ℕ):ℝ)))^2)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

end
end InnerFloorResearch
