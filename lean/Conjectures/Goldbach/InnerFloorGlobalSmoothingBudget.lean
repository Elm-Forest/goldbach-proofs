import Conjectures.Goldbach.InnerFloorFixedBandAnalyticParameters

/-! Global n-based delta and U give an explicit polynomial saving
for the prime-power and smoothed explicit-formula remainders. -/
open Filter
open scoped Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

theorem globalSmoothingBudget
    {n X A h U a c D : ℝ}
    (hn : 3 ≤ n) (hX : 1 ≤ X) (hXn : X ≤ n)
    (hA1 : 1 ≤ A) (hh : 0 < h) (hD : 0 < D)
    (hAp : A ≤ n^a) (hcp : n^c ≤ 2*h)
    (hU : n^(3/2:ℝ) ≤ U)
    (hlog : Real.log (A*U) ≤ 2*Real.log n)
    (he₁ : a+2/3 ≤ c-1/10)
    (he₂ : a-1/6 ≤ c-1/10)
    (he₃ : 3*a-1/6 ≤ c-1/10)
    (he₄ : a+1/2 ≤ c-1/4) :
    let δ := n^(2/3:ℝ)
    let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        A^2*X^2*Real.log (A*U)/(δ*U))+
          2*Real.sqrt (3*X)*Real.log (3*X)
    A*E ≤ (8*D+16)*h*n^(-(1/10):ℝ)*Real.log n := by
  dsimp only
  let δ := n^(2/3:ℝ)
  let L := Real.log n
  let r := n^(-(1/10):ℝ)
  have hnP : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hA : 0 < A := by linarith
  have hδ : 0 < δ := Real.rpow_pos_of_pos hnP _
  have hr : 0 < r := Real.rpow_pos_of_pos hnP _
  have hU0 : 0 < U := (Real.rpow_pos_of_pos hnP _).trans_le hU
  have hL : 0 ≤ L := Real.log_nonneg hn1
  have hLX : Real.log X ≤ L := Real.log_le_log (by linarith) hXn
  have hLX0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hL3 : Real.log (3*X) ≤ 2*L := by
    have H := Real.log_le_log (by linarith : 0 < 3*X)
      (show 3*X ≤ n^2 by nlinarith only [hXn,hn,mul_le_mul_of_nonneg_right hn (show 0 ≤ n by positivity)])
    rw [Real.log_pow] at H
    norm_num at H
    exact H
  have hL30 : 0 ≤ Real.log (3*X) := Real.log_nonneg (by linarith)
  have hreserve (e : ℝ) (he : e ≤ c-1/10) : n^e ≤ 2*h*r := by
    calc
      _ ≤ n^(c-1/10) := Real.rpow_le_rpow_of_exponent_le hn1 he
      _ = n^c*r := by dsimp [r]; rw [← Real.rpow_add hnP]; congr 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcp hr.le
  have hroot : Real.sqrt X ≤ n^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hXn
  have hroot3 : Real.sqrt (3*X) ≤ 2*n^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    have hs : Real.sqrt 3 ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3),Real.sqrt_nonneg 3]
    exact mul_le_mul hs (Real.sqrt_le_sqrt hXn) (Real.sqrt_nonneg _) (by norm_num)
  have h1 : A*δ ≤ 2*h*r := by
    calc
      _ ≤ n^a*n^(2/3:ℝ) := mul_le_mul_of_nonneg_right hAp hδ.le
      _ = n^(a+2/3) := (Real.rpow_add hnP _ _).symm
      _ ≤ _ := hreserve _ he₁
  have h2 : A*Real.sqrt X/δ ≤ 2*h*r := by
    calc
      _ ≤ n^a*n^(1/2:ℝ)/δ :=
        div_le_div_of_nonneg_right
          (mul_le_mul hAp hroot (Real.sqrt_nonneg _) (Real.rpow_nonneg hnP.le _)) hδ.le
      _ = n^(a-1/6) := by
        dsimp [δ]
        rw [← Real.rpow_add hnP,← Real.rpow_sub hnP]
        congr 1 <;> ring
      _ ≤ _ := hreserve _ he₂
  have h3 : A^3*X^2/(δ*U) ≤ 2*h*r := by
    have hden : n^(2/3:ℝ)*n^(3/2:ℝ) ≤ δ*U :=
      mul_le_mul_of_nonneg_left hU hδ.le
    calc
      _ ≤ (n^a)^3*n^2/(n^(2/3:ℝ)*n^(3/2:ℝ)) := by
        apply le_trans (div_le_div_of_nonneg_right
          (mul_le_mul (pow_le_pow_left₀ hA.le hAp 3)
            (pow_le_pow_left₀ (by linarith) hXn 2) (sq_nonneg _) (by positivity))
          (mul_nonneg hδ.le hU0.le))
        exact div_le_div_of_nonneg_left (by positivity)
          (mul_pos (Real.rpow_pos_of_pos hnP _) (Real.rpow_pos_of_pos hnP _)) hden
      _ = n^(3*a-1/6) := by
        rw [← Real.rpow_add hnP,show (n^a)^3=n^(3*a) by
          rw [← Real.rpow_natCast,← Real.rpow_mul hnP.le]
          norm_num; congr 1 <;> ring,
          ← Real.rpow_natCast,← Real.rpow_add hnP,← Real.rpow_sub hnP]
        congr 1 <;> ring
      _ ≤ _ := hreserve _ he₃
  have h4 : A*Real.sqrt (3*X) ≤ 4*h*r := by
    calc
      _ ≤ n^a*(2*n^(1/2:ℝ)) :=
        mul_le_mul hAp hroot3 (Real.sqrt_nonneg _) (Real.rpow_nonneg hnP.le _)
      _ = 2*n^(a+1/2) := by rw [← mul_assoc,mul_comm (n^a) 2,mul_assoc,← Real.rpow_add hnP]
      _ ≤ 2*(2*h*r) := mul_le_mul_of_nonneg_left (hreserve _ (by linarith only [he₄])) (by norm_num)
      _ = _ := by ring
  have b1 := mul_le_mul h1 hLX hLX0 (by positivity : 0 ≤ 2*h*r)
  have b2 := mul_le_mul h2 hLX hLX0 (by positivity : 0 ≤ 2*h*r)
  have b3 := mul_le_mul h3 hlog
    (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hA1
      ((Real.one_le_rpow hn1 (by norm_num : (0:ℝ) ≤ 3/2)).trans hU)))
    (by positivity : 0 ≤ 2*h*r)
  have b4 := mul_le_mul h4 hL3 hL30 (by positivity : 0 ≤ 4*h*r)
  change A*(D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
      A^2*X^2*Real.log (A*U)/(δ*U))+
      2*Real.sqrt (3*X)*Real.log (3*X)) ≤ (8*D+16)*h*r*L
  have hsum :
      (A*δ)*Real.log X+(A*Real.sqrt X/δ)*Real.log X+
      (A^3*X^2/(δ*U))*Real.log (A*U) ≤ 8*h*r*L := by
    linarith only [b1,b2,b3]
  have H := mul_le_mul_of_nonneg_left hsum hD.le
  have H4 := mul_le_mul_of_nonneg_left b4 (show (0:ℝ) ≤ 2 by norm_num)
  convert add_le_add H H4 using 1 <;> ring

end
end InnerFloorResearch
