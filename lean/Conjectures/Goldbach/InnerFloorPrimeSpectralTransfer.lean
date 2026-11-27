import Conjectures.Goldbach.InnerFloorFullSpectrum
import Conjectures.Goldbach.InnerFloorPrimeWeightTransfer

/-!
Use the smoothed explicit formula directly for the log-prime window.
The von Mangoldt-to-prime correction is absorbed pointwise in E; there
is no extra integral triangle or integrability obligation for the
arithmetic step functions.
-/
open Finset MeasureTheory Filter
open scoped Classical Interval Topology
open OAI.Ostmann V1e V6i V7e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem primitivePrimeEnergyFromZeros :
    ∃ D : ℝ, 0 < D ∧ ∀ (Q : ℕ), 1 ≤ Q →
      ∀ (X δ U : ℝ) (h : ℕ), 4 ≤ X → (h:ℝ) ≤ X →
      1 ≤ δ → δ ≤ X/2 → 2 ≤ U → (Q:ℝ) ≤ X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) + 2*Real.sqrt (3*X)*Real.log (3*X)
      (∑ χ∈F, ∫ y in X..2*X, ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        2*X*(Q:ℝ)^2*E^2 +
          2*(∑ χ∈F, ∫ y in X-δ..2*X,
            ‖∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)‖^2) := by
  obtain ⟨D,hD,hformula⟩ := PolynomialWindow.nonprincipalWindowFormulaPolynomial
  refine ⟨D,hD,?_⟩
  intro Q hQ X δ U h hX hhX hδ hδX hU hQX F hF
  dsimp only
  let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U)) + 2*Real.sqrt (3*X)*Real.log (3*X)
  let f (χ : PrimitiveComplexCharacter) (y : ℝ) :=
    ∑ i∈(V1 χ).V14 U, Ve y (h:ℝ) ((V1 χ).zeros i)
  have hE : 0 ≤ E := by
    have hL : 0≤Real.log X := Real.log_nonneg (by linarith)
    have hQr : (1:ℝ)≤Q := by exact_mod_cast hQ
    have hL2 : 0≤Real.log ((Q:ℝ)*U) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQr (by linarith))
    have hL3 : 0≤Real.log (3*X) := Real.log_nonneg (by linarith)
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
      (∫ y in X..2*X, ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        2*X*E^2+2*(∫ y in X-δ..2*X,‖f χ y‖^2) :=
    windowFormulaEnergy (fun y => InnerFloorAP.centeredPrimeSum χ.character y h) (f χ) (by linarith) (by linarith) hE
      (hcont χ) (fun y hy =>
        by
          have ha := hformula Q hQ X y δ U h hX hy hhX hδ hδX hU hQX χ (hF χ hχ)
          have hb := (centeredPrimeWindowError χ h
            (by linarith [hy.1]) (show y+(h:ℝ)≤3*X by linarith [hy.2])).trans
            (Chebyshev.psi_sub_theta_le (show 1≤3*X by linarith))
          have hdiff : ‖InnerFloorAP.centeredPrimeSum χ.character y h - V4q χ h y‖ ≤
              2*Real.sqrt (3*X)*Real.log (3*X) := by
            rw [norm_sub_rev]
            exact hb
          have hsplit : InnerFloorAP.centeredPrimeSum χ.character y h + V3q (f χ) δ y =
              (V4q χ h y + V3q (f χ) δ y) +
                (InnerFloorAP.centeredPrimeSum χ.character y h - V4q χ h y) := by abel
          rw [hsplit]
          exact (norm_add_le _ _).trans (add_le_add ha hdiff))
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


/-- The enlarged smoothing interval is covered by two adjacent dyadic
intervals, so no unproved estimate on a non-dyadic segment is needed. -/
theorem enlargedZeroWindowEnergy_le
    (F : Finset PrimitiveComplexCharacter) (U X h δ : ℝ)
    (hX : 0 < X) (hh : 0 ≤ h) (hhX : h≤X/2)
    (hδ : 0≤δ) (hδX : δ≤X/2) :
    (∑ χ∈F, ∫ y in X-δ..2*X, ‖zeroWindow χ ((V1 χ).V14 U) h y‖^2) ≤
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) (X/2) h +
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) X h := by
  unfold zeroFamilyEnergy
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro χ _
  let f (y:ℝ) := ‖zeroWindow χ ((V1 χ).V14 U) h y‖^2
  have hcont : ContinuousOn f (Set.Icc (X/2) (2*X)) := by
    unfold f
    apply ContinuousOn.pow
    unfold zeroWindow
    apply ContinuousOn.norm
    apply continuousOn_finsetSum
    intro i hi
    unfold Ve
    simp only [div_eq_mul_inv]
    apply ContinuousOn.mul _ continuousOn_const
    apply ContinuousOn.sub
    · intro y hy
      have hp : y+h≠0 := by linarith [hy.1]
      have hc : ContinuousAt (fun t:ℝ => t+h) y :=
        (continuous_id.add continuous_const).continuousAt
      have hcomp : ContinuousAt (fun t:ℝ => ((t+h:ℝ):ℂ)^((V1 χ).zeros i)) y :=
        ContinuousAt.comp (f := fun t : ℝ => t+h) (x := y)
          (Complex.continuousAt_ofReal_cpow_const (y+h) ((V1 χ).zeros i) (Or.inr hp)) hc
      exact hcomp.continuousWithinAt
    · intro y hy
      exact (Complex.continuousAt_ofReal_cpow_const y ((V1 χ).zeros i)
        (Or.inr (by linarith [hy.1] : y≠0))).continuousWithinAt
  have hi : IntervalIntegrable f volume (X/2) (2*X) :=
    hcont.intervalIntegrable_of_Icc (by linarith)
  have hsplit : (∫ y in X/2..2*X,f y) =
      (∫ y in X/2..X,f y)+(∫ y in X..2*X,f y) := by
    have h₁ : IntervalIntegrable f volume (X/2) X :=
      (hcont.mono (Set.Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc (by linarith)
    have h₂ : IntervalIntegrable f volume X (2*X) :=
      (hcont.mono (Set.Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc (by linarith)
    exact (intervalIntegral.integral_add_adjacent_intervals h₁ h₂).symm
  change (∫ y in X-δ..2*X,f y) ≤
    (∫ y in X/2..2*(X/2),f y)+(∫ y in X..2*X,f y)
  rw [show 2*(X/2)=X by ring,← hsplit]
  rw [intervalIntegral.integral_of_le (by linarith : X-δ≤2*X),
    intervalIntegral.integral_of_le (by linarith : X/2≤2*X)]
  have hI : IntegrableOn f (Set.Ioc (X/2) (2*X)) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : X/2≤2*X)).1 hi
  exact setIntegral_mono_set hI (Filter.Eventually.of_forall fun _ => sq_nonneg _)
    (Filter.Eventually.of_forall fun _ hy => ⟨by linarith [hy.1],hy.2⟩)


/-- Actual prime energy, with an explicit and isolated exceptional
spectral residual. Both dyadic spectral inputs are theorems, not
hypotheses. The only potentially large terms are the two bad packets. -/
theorem primitivePrimeEnergyWithResidual (B : ℕ) :
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧ ∃ X₀ : ℝ, 4 ≤ X₀ ∧
      ∀ (Q K : ℕ) (X δ : ℝ) (h : ℕ), 1 ≤ Q → X₀ ≤ X → 0 < h →
      (h:ℝ) ≤ X/2 → 1 ≤ δ → δ ≤ X/2 → (Q:ℝ) ≤ X →
      (Q:ℝ)^2/((h:ℝ)/(X/2)) ≤ (X/2)^(5/12:ℝ) →
      (Q:ℝ)^2/((h:ℝ)/X) ≤ X^(5/12:ℝ) →
      Real.log ((Q:ℝ)*(2:ℝ)^(K+1)) ≤ 2*Real.log (X/2) →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F,χ.modulus≤Q) →
      let U := (2:ℝ)^(K+1)
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (Q:ℝ)^2*X^2*Real.log ((Q:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*X)*Real.log (3*X)
      let R (Y:ℝ) := zeroFamilyEnergy F
        (fun χ => rightBadIndices χ U (1-V1l.V2j (B+4) Y)) Y h
      (∑ χ∈F, ∫ y in X..2*X, ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) ≤
        2*X*(Q:ℝ)^2*E^2+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*(X/2)/(Real.log (X/2))^B+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*X/(Real.log X)^B+
        6*(R (X/2)+R X) := by
  obtain ⟨D,hD,hd⟩ := primitivePrimeEnergyFromZeros
  obtain ⟨C,hC,Y₀,hY₀,hc⟩ := fullSpectrumEnergyWithResidual B
  refine ⟨D,C,hD,hC,max 4 (2*Y₀),le_max_left ..,?_⟩
  intro Q K X δ h hQ hX hh hhX hδ hδX hQX hscale₁ hscale₂ hlog F hF
  dsimp only
  let U := (2:ℝ)^(K+1)
  have hX4 : 4≤X := (le_max_left _ _).trans hX
  have hXp : 0 < X := by linarith
  have hY : Y₀≤X/2 := by linarith [(le_max_right (4:ℝ) (2*Y₀)).trans hX]
  have hY' : Y₀≤X := by linarith
  have hU : 2≤U := by
    dsimp [U]
    rw [pow_succ]
    have hk : (1:ℝ)≤(2:ℝ)^K := one_le_pow₀ (by norm_num)
    nlinarith only [hk]
  have hh' : (0:ℝ) < h := by exact_mod_cast hh
  have hlog' : Real.log ((Q:ℝ)*U)≤2*Real.log X :=
    hlog.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith : 0 < X/2) (by linarith)) (by norm_num))
  have he := hd Q hQ X δ U h hX4 (by linarith) hδ hδX hU hQX F hF
  dsimp only at he
  have hz := enlargedZeroWindowEnergy_le F U X h δ hXp hh'.le hhX (by linarith) hδX
  have h1 := hc Q K (X/2) h hQ hY hh' hhX hscale₁ hlog F hF
  have h2 := hc Q K X h hQ hY' hh' (by linarith) hscale₂ hlog' F hF
  dsimp only at h1 h2
  change (∑ χ∈F, ∫ y in X-δ..2*X,‖zeroWindow χ ((V1 χ).V14 U) h y‖^2) ≤ _ at hz
  unfold zeroWindow at hz
  dsimp only [U] at he hz
  have hZ := hz.trans (add_le_add h1 h2)
  have hT := he.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hZ (by norm_num : (0:ℝ) ≤ 2)))
  exact hT.trans_eq (by ring)

end
end InnerFloorResearch
