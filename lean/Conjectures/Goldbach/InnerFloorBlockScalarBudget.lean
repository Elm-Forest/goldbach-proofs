import Mathlib

/-! Scalar assembly of the explicit-formula residual, good-zero energy
and principal energy. The only large parameter is the global logarithm L. -/
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem logDenominatorBudget {L l : ℝ} (hL : 0 < L) (hl : L/2 ≤ l) (k : ℕ) :
    1/l^k ≤ (2:ℝ)^k/L^k := by
  have hlp : 0 < l := by linarith
  apply (div_le_div_iff₀ (pow_pos hlp _) (pow_pos hL _)).2
  have hp : L^k ≤ (2*l)^k := pow_le_pow_left₀ hL.le (by linarith) _
  rw [mul_pow] at hp
  simpa only [one_mul] using hp

theorem blockScalarBudget {n X A h E K D C P L l₁ l₂ : ℝ}
    (hn : 1 ≤ n) (hX : 0 ≤ X) (hA : 0 ≤ A) (hh : 0 ≤ h)
    (hE : 0 ≤ E) (hK : 0 ≤ K) (hD : 0 ≤ D) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hL : 0 < L) (h₁ : L/2 ≤ l₁) (h₂ : L/2 ≤ l₂)
    (hk : K ≤ 5*L)
    (he : A*E ≤ (8*D+16)*h*n^(-(1/10):ℝ)*L)
    (hsmall : L^10 ≤ n^(1/5:ℝ)) :
    2*X*A^2*E^2 + 2*C*K^2*h^2*(X/2)/l₁^10 +
      2*C*K^2*h^2*X/l₂^10 + P*h^2*X/l₂^8 ≤
      (2*(8*D+16)^2+76800*C+256*P)*h^2*X/L^8 := by
  have hnP : 0 < n := by linarith
  have h₁p : 0 < l₁ := by linarith
  have h₂p : 0 < l₂ := by linarith
  have hp := pow_le_pow_left₀ (mul_nonneg hA hE) he 2
  have hr : (n^(-(1/10):ℝ))^2 = n^(-(1/5):ℝ) := by
    rw [pow_two,← Real.rpow_add hnP]
    congr 1 <;> ring
  have haux : n^(-(1/5):ℝ)*L^10 ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg hnP.le (-(1/5):ℝ))
    rw [← Real.rpow_add hnP,show -(1/5:ℝ)+1/5=0 by ring,Real.rpow_zero] at H
    exact H
  have herror : (A*E)^2 ≤ (8*D+16)^2*h^2/L^8 := by
    apply (le_div_iff₀ (pow_pos hL _)).2
    calc
      _ ≤ ((8*D+16)*h*n^(-(1/10):ℝ)*L)^2*L^8 :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = ((8*D+16)^2*h^2)*(n^(-(1/5):ℝ)*L^10) := by
        simp only [mul_pow,hr]
        ring
      _ ≤ _ := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left haux (show 0 ≤ (8*D+16)^2*h^2 by positivity)
  have hk' : K^2 ≤ 25*L^2 := by
    calc
      _ ≤ (5*L)^2 := pow_le_pow_left₀ hK hk 2
      _ = _ := by ring
  have hnorm (l : ℝ) (hl : L/2 ≤ l) :
      K^2/l^10 ≤ 25600/L^8 := by
    have hlp : 0 < l := by linarith
    have H := logDenominatorBudget hL hl 10
    norm_num at H
    calc
      _ ≤ (25*L^2)*(1024/L^10) := by
        rw [div_eq_mul_inv]
        apply mul_le_mul hk' _ (by positivity) (by positivity)
        simpa only [one_div] using H
      _ = _ := by field_simp; ring
  have hPden := logDenominatorBudget hL h₂ 8
  norm_num at hPden
  have t1 := mul_le_mul_of_nonneg_left herror (show 0 ≤ 2*X by positivity)
  have t2 := mul_le_mul_of_nonneg_left (hnorm l₁ h₁)
    (show 0 ≤ C*h^2*X by positivity)
  have t3 := mul_le_mul_of_nonneg_left (hnorm l₂ h₂)
    (show 0 ≤ 2*C*h^2*X by positivity)
  have t4 := mul_le_mul_of_nonneg_left hPden (show 0 ≤ P*h^2*X by positivity)
  convert add_le_add (add_le_add (add_le_add t1 t2) t3) t4 using 1 <;> ring

end
end InnerFloorResearch
