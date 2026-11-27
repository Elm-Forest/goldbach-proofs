import Conjectures.Goldbach.InnerFloorFixedBandBoundary

/-! Boundary term is negligible at any fixed logarithmic scale.
The only input about h is its fixed polynomial margin below n. -/
open Filter Finset InnerFloorLinearTotient
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem eventualFixedBandBoundarySmall (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ A h : ℕ,
      1 ≤ A → A ≤ n+2 → 0 < h → (A:ℝ)^2 ≤ (h:ℝ) →
      (h:ℝ) ≤ (n:ℝ)^(99/100:ℝ) →
      4*((2*h+2*h:ℕ):ℝ)*boundaryWindowBudget A n h/(h:ℝ)^2 ≤
        ε*(n:ℝ)/(Real.log n)^k := by
  let C : ℝ := 16*(1024+18*weightConstant^2)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hlog1 : ∀ᶠ n : ℕ in atTop, (1:ℝ) ≤ Real.log (n:ℝ) := by
    filter_upwards [eventually_ge_atTop (4:ℕ)] with n hn
    have H := Real.log_le_log (by norm_num : (0:ℝ) < 4)
      (show (4:ℝ) ≤ n by exact_mod_cast hn)
    have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num
    linarith [Real.log_two_gt_d9]
  filter_upwards [eventually_ge_atTop (4:ℕ),hlog1,
    GoldbachGRHBudget.eventually_log_pow_le (k+2) (1/100) (ε/C)
      (by norm_num) (div_pos hε hC)] with n hn hL hs
  intro A h hA hAn hh hA2 hhcap
  have hnR : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hnP : (0:ℝ) < n := by linarith
  have hL0 : 0 < Real.log (n:ℝ) := by linarith
  have hN : ((n+2:ℕ):ℝ) ≤ (n:ℝ)^2 := by
    push_cast
    nlinarith only [hnR,sq_nonneg ((n:ℝ)-2)]
  have hlogN := Real.log_le_log (by positivity : (0:ℝ) < ((n+2:ℕ):ℝ)) hN
  rw [Real.log_pow] at hlogN
  norm_num at hlogN
  have hlogA := Real.log_le_log
    (by exact_mod_cast (show 0 < A by omega)) (show (A:ℝ) ≤ ((n+2:ℕ):ℝ) by exact_mod_cast hAn)
  have hlogN0 : 0 ≤ Real.log ((n+2:ℕ):ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n+2 by omega))
  have hW := weightConstant_nonneg
  have h1 : weightConstant*(1+Real.log ((n+2:ℕ):ℝ)) ≤
      3*weightConstant*Real.log (n:ℝ) := by
    calc
      _ ≤ weightConstant*(3*Real.log (n:ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hW
      _ = _ := by ring
  have hsq1 := pow_le_pow_left₀ hlogN0 hlogN 2
  have hsq2 := pow_le_pow_left₀
    (show 0 ≤ weightConstant*(1+Real.log ((n+2:ℕ):ℝ)) by positivity) h1 2
  have hh0 : (0:ℝ) ≤ h := Nat.cast_nonneg _
  have hb := fixedBand_boundary_scalar A n h hA hh hA2 hlogA
  have hcoef : 16*(256*(Real.log ((n+2:ℕ):ℝ))^2+
        2*(weightConstant*(1+Real.log ((n+2:ℕ):ℝ)))^2) ≤
        C*(Real.log n)^2 := by
    dsimp [C]
    nlinarith only [hsq1,hsq2]
  apply hb.trans
  have hmid : 16*(h:ℝ)*(256*(Real.log ((n+2:ℕ):ℝ))^2+
        2*(weightConstant*(1+Real.log ((n+2:ℕ):ℝ)))^2) ≤
        C*(h:ℝ)*(Real.log n)^2 := by
    have H := mul_le_mul_of_nonneg_left hcoef hh0
    nlinarith only [H]
  apply hmid.trans
  apply (le_div_iff₀ (pow_pos hL0 k)).2
  have hs' : C*(Real.log n)^(k+2) ≤ ε*(n:ℝ)^(1/100:ℝ) := by
    calc
      _ ≤ C*((ε/C)*(n:ℝ)^(1/100:ℝ)) := mul_le_mul_of_nonneg_left hs hC.le
      _ = _ := by field_simp
  calc
    C*(h:ℝ)*(Real.log n)^2*(Real.log n)^k =
        (h:ℝ)*(C*(Real.log n)^(k+2)) := by rw [pow_add]; ring
    _ ≤ (n:ℝ)^(99/100:ℝ)*(ε*(n:ℝ)^(1/100:ℝ)) :=
      mul_le_mul hhcap hs' (by positivity) (Real.rpow_nonneg hnP.le _)
    _ = ε*(n:ℝ) := by
      rw [← mul_assoc,mul_comm ((n:ℝ)^(99/100:ℝ)) ε,mul_assoc,← Real.rpow_add hnP]
      norm_num

end
end InnerFloorResearch
