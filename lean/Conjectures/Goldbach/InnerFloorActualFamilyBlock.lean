import Conjectures.Goldbach.InnerFloorPrimitiveFamilyBridge
import Conjectures.Goldbach.InnerFloorPrincipalPrimeWindow
import Conjectures.Goldbach.InnerFloorDiscreteWindowEnergy
import Conjectures.Goldbach.InnerFloorPrimeSpectralTransfer
import Conjectures.Goldbach.InnerFloorUniformStripBridge

/-!
The actual arithmetic family on an integer dyadic block, including the
principal character. This uses the exact step-integral identity, rather
than assuming measurability of a new family or losing a logarithm.
The nonprincipal exceptional spectral residual is not removed here.
-/
open Finset MeasureTheory Filter OAI.Ostmann
open scoped Classical Interval Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

theorem actualNonprincipalBlock_eq_integral (A X h : ℕ) :
    (∑ y∈Ico X (2*X),∑ χ∈analyticPrimitiveFamily A,
        ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) =
      ∑ χ∈analyticPrimitiveFamily A,
        ∫ y in (X:ℝ)..2*(X:ℝ), ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro χ hχ
  have H := integer_step_integral X (2*X) (by omega)
    (fun y : ℝ => ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2)
    (fun y : ℕ => ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2)
    (by
      intro k y hy
      rw [centeredPrimeSum_on_unit χ.character k h hy])
  push_cast at H
  exact H.symm

theorem actualPrimitiveBlockWithNonprincipal :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 2≤X₀ ∧
      ∀ (A X h : ℕ), X₀≤(X:ℝ) → h≤X →
        (2*(X:ℝ))^(4/5:ℝ)≤(h:ℝ) →
      (∑ y∈Ico X (2*X), ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
      (∑ χ∈analyticPrimitiveFamily A,
        ∫ y in (X:ℝ)..2*(X:ℝ), ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) +
      C*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
  obtain ⟨C,hC,X₀,hX₀,hCbound⟩ := principalPrimeWindowLogFour
  refine ⟨C^2,by positivity,X₀,hX₀,?_⟩
  intro A X h hX hhX hhlow
  have hX2 : (2:ℝ)≤X := hX₀.trans hX
  have hXp : (0:ℝ) < X := by linarith
  have hlogX : 0 < Real.log (X:ℝ) := Real.log_pos (by linarith)
  let P (y : ℕ) := ‖InnerFloorAP.centeredPrimeSum (1:DirichletCharacter ℂ 1) y h‖^2
  have hp (y : ℕ) (hy : y∈Ico X (2*X)) :
      P y≤(C*(h:ℝ)/(Real.log (X:ℝ))^4)^2 := by
    have hy₁ : (X:ℝ)≤y := by exact_mod_cast (mem_Ico.mp hy).1
    have hy₂ : (y:ℝ)≤2*(X:ℝ) := by exact_mod_cast (mem_Ico.mp hy).2.le
    have hylow : (y:ℝ)^(4/5:ℝ)≤(h:ℝ) :=
      (Real.rpow_le_rpow (by positivity) hy₂ (by norm_num)).trans hhlow
    have hyh : (h:ℝ)≤y := (by exact_mod_cast hhX : (h:ℝ)≤X).trans hy₁
    have he := hCbound y (hX.trans hy₁) h hylow hyh (1:DirichletCharacter ℂ 1)
    have hl : Real.log (X:ℝ)≤Real.log (y:ℝ) := Real.log_le_log hXp hy₁
    have hden : (Real.log (X:ℝ))^4≤(Real.log (y:ℝ))^4 :=
      pow_le_pow_left₀ hlogX.le hl 4
    have hb : ‖InnerFloorAP.centeredPrimeSum (1:DirichletCharacter ℂ 1) y h‖ ≤
        C*(h:ℝ)/(Real.log (X:ℝ))^4 :=
      he.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hlogX _) hden)
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hP : (∑ y∈Ico X (2*X),P y) ≤
      C^2*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
    calc
      _ ≤ ∑ _y∈Ico X (2*X),(C*(h:ℝ)/(Real.log (X:ℝ))^4)^2 := sum_le_sum hp
      _ = _ := by
        rw [sum_const,nsmul_eq_mul,Nat.card_Ico,show 2*X-X=X by omega]
        ring
  calc
    _ ≤ ∑ y∈Ico X (2*X),
        ((∑ χ∈analyticPrimitiveFamily A,
          ‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2)+P y) :=
      sum_le_sum fun y _ => primitiveEnergy_le_analyticFamily A y h
    _ = (∑ χ∈analyticPrimitiveFamily A,
        ∫ y in (X:ℝ)..2*(X:ℝ),‖InnerFloorAP.centeredPrimeSum χ.character y h‖^2) +
        ∑ y∈Ico X (2*X),P y := by
      rw [sum_add_distrib,actualNonprincipalBlock_eq_integral]
    _ ≤ _ := add_le_add le_rfl hP

/-- Direct actual arithmetic block bound. No unknown arithmetic family
or all-residue model appears: only the two explicitly defined spectral
residuals remain. -/
theorem actualPrimitiveBlockWithResidual (B : ℕ) :
    ∃ D C P : ℝ, 0 < D ∧ 0 < C ∧ 0 < P ∧ ∃ X₀ : ℝ, 4≤X₀ ∧
      ∀ (A X h K : ℕ) (δ : ℝ), 1≤A → X₀≤(X:ℝ) → 0 < h →
      (2*(X:ℝ))^(4/5:ℝ)≤(h:ℝ) → (h:ℝ)≤(X:ℝ)/2 →
      1≤δ → δ≤(X:ℝ)/2 → A≤X →
      (A:ℝ)^2/((h:ℝ)/((X:ℝ)/2))≤((X:ℝ)/2)^(5/12:ℝ) →
      (A:ℝ)^2/((h:ℝ)/(X:ℝ))≤(X:ℝ)^(5/12:ℝ) →
      Real.log ((A:ℝ)*(2:ℝ)^(K+1))≤2*Real.log ((X:ℝ)/2) →
      let U := (2:ℝ)^(K+1)
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (A:ℝ)^2*(X:ℝ)^2*Real.log ((A:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*(X:ℝ))*Real.log (3*(X:ℝ))
      let R (Y:ℝ) := zeroFamilyEnergy (analyticPrimitiveFamily A)
        (fun χ => rightBadIndices χ U (1-V1l.V2j (B+4) Y)) Y h
      (∑ y∈Ico X (2*X),∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
        2*(X:ℝ)*(A:ℝ)^2*E^2+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*((X:ℝ)/2)/(Real.log ((X:ℝ)/2))^B+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*(X:ℝ)/(Real.log X)^B+
        6*(R ((X:ℝ)/2)+R X)+
        P*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
  obtain ⟨D,C,hD,hC,X₁,hX₁,hbound⟩ := primitivePrimeEnergyWithResidual B
  obtain ⟨P,hP,X₂,hX₂,hprincipal⟩ := actualPrimitiveBlockWithNonprincipal
  refine ⟨D,C,P,hD,hC,hP,max X₁ X₂,hX₁.trans (le_max_left ..),?_⟩
  intro A X h K δ hA hX hh hlow hhX hδ hδX hAX hs₁ hs₂ hlog
  dsimp only
  have hX₁' : X₁≤(X:ℝ) := (le_max_left _ _).trans hX
  have hX₂' : X₂≤(X:ℝ) := (le_max_right _ _).trans hX
  have hh' : h≤X := by
    exact_mod_cast hhX.trans (by linarith [Nat.cast_nonneg (α:=ℝ) X] : (X:ℝ)/2≤X)
  have H := hprincipal A X h hX₂' hh' hlow
  have G := hbound A K X δ h hA hX₁' hh hhX hδ hδX
    (by exact_mod_cast hAX) hs₁ hs₂ hlog (analyticPrimitiveFamily A)
      (analyticPrimitiveFamily_modulus A)
  dsimp only at G
  exact H.trans (add_le_add G le_rfl)

end
end InnerFloorResearch
