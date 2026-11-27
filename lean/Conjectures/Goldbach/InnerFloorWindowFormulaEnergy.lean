import Conjectures.Goldbach.InnerFloorPolynomialWindow

/-!
Local energy transfer from the polynomial-modulus explicit formula.
The residual is kept explicit; no zero-free hypothesis is used.
This connects the analytic formula to an actual arithmetic-window L² bound.
-/

open Finset MeasureTheory
open scoped Interval Classical
open OAI.Ostmann V1e V6i V7e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem windowFormulaEnergy (g f : ℝ → ℂ) {X δ E : ℝ}
    (hX : 0 ≤ X) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hf : ContinuousOn f (Set.Icc (X-δ) (2*X)))
    (hres : ∀ y ∈ Set.Icc X (2*X), ‖g y + V3q f δ y‖ ≤ E) :
    (∫ y in X..2*X, ‖g y‖^2) ≤
      2*X*E^2 + 2*(∫ y in X-δ..2*X, ‖f y‖^2) := by
  have hXX : X ≤ 2*X := by linarith
  obtain ⟨hQ,hFubini⟩ := V16e (fun u => ‖f u‖^2) X δ hX hδ.le
    (hf.norm.pow 2) (fun _ _ => sq_nonneg _)
  have hp : ∀ y ∈ Set.Icc X (2*X),
      ‖g y‖^2 ≤ 2*E^2 + (2/δ)*(∫ u in y-δ..y, ‖f u‖^2) := by
    intro y hy
    have hc : ContinuousOn f (Set.Icc (y-δ) y) := hf.mono (by
      intro u hu
      exact ⟨by linarith [hy.1,hu.1],by linarith [hy.2,hu.2]⟩)
    have hs := Vl2.V1gz f (y-δ) y (by linarith) hc
    have hn : ‖V3q f δ y‖^2 ≤ (1/δ)*(∫ u in y-δ..y, ‖f u‖^2) := by
      have he : ‖V3q f δ y‖^2 =
          (δ⁻¹)^2*‖∫ u in y-δ..y,f u‖^2 := by
        rw [V3q,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hδ.le,mul_pow]
      rw [he]
      apply (mul_le_mul_of_nonneg_left hs (sq_nonneg (δ⁻¹))).trans_eq
      field_simp
      <;> ring
    have hnorm : ‖g y‖ ≤ E + ‖V3q f δ y‖ := by
      have h := norm_sub_le (g y + V3q f δ y) (V3q f δ y)
      rw [add_sub_cancel_right] at h
      linarith [hres y hy]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hs' : (E + ‖V3q f δ y‖)^2 ≤ 2*E^2+2*‖V3q f δ y‖^2 := by
      nlinarith [sq_nonneg (E-‖V3q f δ y‖)]
    refine hsq.trans (hs'.trans ?_)
    calc
      _ ≤ 2*E^2+2*((1/δ)*(∫ u in y-δ..y, ‖f u‖^2)) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hn (by norm_num : (0:ℝ)≤2)) _
      _ = _ := by ring
  have hi : (∫ y in X..2*X, ‖g y‖^2) ≤
      ∫ y in X..2*X, 2*E^2 + (2/δ)*(∫ u in y-δ..y, ‖f u‖^2) := by
    rw [intervalIntegral.integral_of_le hXX,intervalIntegral.integral_of_le hXX]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (intervalIntegrable_const.add (hQ.const_mul (2/δ))).1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact hp y ⟨hy.1.le,hy.2⟩
  rw [intervalIntegral.integral_add intervalIntegrable_const (hQ.const_mul (2/δ)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hi
  simp only [smul_eq_mul] at hi
  calc
    _ ≤ (2*X-X)*(2*E^2)+(2/δ)*(∫ y in X..2*X,∫ u in y-δ..y,‖f u‖^2) := hi
    _ ≤ (2*X-X)*(2*E^2)+(2/δ)*(δ*(∫ u in X-δ..2*X,‖f u‖^2)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hFubini (by positivity : 0≤(2:ℝ)/δ)) _
    _ = _ := by field_simp; ring

/-- The actual nonprincipal von Mangoldt short-window family is bounded by
the explicit formula residual plus the full zero-window energy. -/
theorem primitiveWindowEnergyFromZeros :
    ∃ D : ℝ, 0 < D ∧ ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (X δ U : ℝ) (h : ℕ), 4 ≤ X → (h:ℝ) ≤ X →
      1 ≤ δ → δ ≤ X/2 → 2 ≤ U → (Q:ℝ) ≤ X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U))
      (∑ χ∈F, ∫ y in X..2*X, ‖V4q χ h y‖^2) ≤
        2*X*(Q:ℝ)^2*E^2 +
          2*(∑ χ∈F, ∫ y in X-δ..2*X,
            ‖∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)‖^2) := by
  obtain ⟨D,hD,hformula⟩ := PolynomialWindow.nonprincipalWindowFormulaPolynomial
  refine ⟨D,hD,?_⟩
  intro Q hQ X δ U h hX hhX hδ hδX hU hQX F hF
  dsimp only
  let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U))
  let f (χ : PrimitiveComplexCharacter) (y : ℝ) :=
    ∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)
  have hE : 0 ≤ E := by
    have hL : 0≤Real.log X := Real.log_nonneg (by linarith)
    have hQr : (1:ℝ)≤Q := by exact_mod_cast hQ
    have hL2 : 0≤Real.log ((Q:ℝ)*U) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQr (by linarith))
    dsimp [E]
    positivity
  have hcont (χ : PrimitiveComplexCharacter) :
      ContinuousOn (f χ) (Set.Icc (X-δ) (2*X)) := by
    unfold f
    apply continuousOn_finsetSum
    intro i hi
    unfold Ve
    simp only [div_eq_mul_inv]
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub
    · intro y hy
      have hp : y+(h:ℝ) ≠ 0 := by linarith [hy.1, Nat.cast_nonneg (α := ℝ) h]
      have hc : ContinuousAt (fun t:ℝ => t+(h:ℝ)) y :=
        (continuous_id.add continuous_const).continuousAt
      have hcomp : ContinuousAt (fun t : ℝ => ((t+(h:ℝ):ℝ):ℂ)^((V1 χ).zeros i)) y :=
        ContinuousAt.comp (f := fun t : ℝ => t+(h:ℝ)) (x := y)
          (Complex.continuousAt_ofReal_cpow_const (y+(h:ℝ)) ((V1 χ).zeros i) (Or.inr hp)) hc
      exact hcomp.continuousWithinAt
    · intro y hy
      exact (Complex.continuousAt_ofReal_cpow_const y ((V1 χ).zeros i)
        (Or.inr (by linarith [hy.1] : y≠0))).continuousWithinAt
  have hterm (χ : PrimitiveComplexCharacter) (hχ : χ∈F) :
      (∫ y in X..2*X, ‖V4q χ h y‖^2) ≤
        2*X*E^2+2*(∫ y in X-δ..2*X,‖f χ y‖^2) :=
    windowFormulaEnergy (V4q χ h) (f χ) (by linarith) (by linarith) hE
      (hcont χ) (fun y hy =>
        hformula Q hQ X y δ U h hX hy hhX hδ hδX hU hQX χ (hF χ hχ))
  have hcard : (F.card:ℝ)≤(Q:ℝ)^2 := by exact_mod_cast V14i F Q hF
  change _ ≤ 2*X*(Q:ℝ)^2*E^2 + 2*(∑ χ∈F, ∫ y in X-δ..2*X,‖f χ y‖^2)
  calc
    _ ≤ ∑ χ∈F, (2*X*E^2+2*(∫ y in X-δ..2*X,‖f χ y‖^2)) :=
      sum_le_sum hterm
    _ = (F.card:ℝ)*(2*X*E^2)+2*(∑ χ∈F,∫ y in X-δ..2*X,‖f χ y‖^2) := by
      rw [sum_add_distrib,← mul_sum]
      simp only [sum_const,nsmul_eq_mul]
      rw [← mul_sum]
      ring
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right hcard (by positivity : 0≤2*X*E^2)
      linarith

end
end InnerFloorResearch
