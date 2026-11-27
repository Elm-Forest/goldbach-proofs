import Conjectures.Goldbach.InnerFloorActualFamilyBlock

/-! The actual primitive arithmetic family estimate with the sole
remaining analytic input, a uniform positive zero-free strip.
This is an implication, not a proof of the strip or frozen floor. -/
open Filter Finset MeasureTheory OAI.Ostmann
open scoped Classical Interval Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem actualPrimitiveBlockOfUniformStrip {σ : ℝ} (hσ : σ < 1)
    (hs : DirichletUniformStrip σ) (B : ℕ) :
    ∃ D C P : ℝ, 0 < D ∧ 0 < C ∧ 0 < P ∧ ∃ X₀ : ℝ, 4 ≤ X₀ ∧
      ∀ (A X h K : ℕ) (δ : ℝ), 1 ≤ A → X₀ ≤ (X:ℝ) → 0 < h →
      (2*(X:ℝ))^(4/5:ℝ) ≤ (h:ℝ) → (h:ℝ) ≤ (X:ℝ)/2 →
      1 ≤ δ → δ ≤ (X:ℝ)/2 → A ≤ X →
      (A:ℝ)^2/((h:ℝ)/((X:ℝ)/2)) ≤ ((X:ℝ)/2)^(5/12:ℝ) →
      (A:ℝ)^2/((h:ℝ)/(X:ℝ)) ≤ (X:ℝ)^(5/12:ℝ) →
      Real.log ((A:ℝ)*(2:ℝ)^(K+1)) ≤ 2*Real.log ((X:ℝ)/2) →
      let U := (2:ℝ)^(K+1)
      let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (A:ℝ)^2*(X:ℝ)^2*Real.log ((A:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*(X:ℝ))*Real.log (3*(X:ℝ))
      (∑ y∈Ico X (2*X),∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
        2*(X:ℝ)*(A:ℝ)^2*E^2+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*((X:ℝ)/2)/(Real.log ((X:ℝ)/2))^B+
        2*C*((K+1:ℕ):ℝ)^2*(h:ℝ)^2*(X:ℝ)/(Real.log X)^B+
        P*(h:ℝ)^2*(X:ℝ)/(Real.log X)^8 := by
  obtain ⟨D,C,P,hD,hC,hP,X₁,hX₁,hbound⟩ := actualPrimitiveBlockWithResidual B
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp
    (eventually_badIndices_empty_of_uniform_gap (B+4) σ hσ
      (uniformStrip_enumeratedGap hs))
  refine ⟨D,C,P,hD,hC,hP,max X₁ (2*max X₂ 1),hX₁.trans (le_max_left ..),?_⟩
  intro A X h K δ hA hX hh hlow hhX hδ hδX hAX hs₁ hs₂ hlog
  have hx₁ : X₁ ≤ (X:ℝ) := (le_max_left _ _).trans hX
  have hx₂ : X₂ ≤ (X:ℝ)/2 := by
    have H := (le_max_right X₁ (2*max X₂ 1)).trans hX
    linarith only [H,le_max_left X₂ 1]
  have hx₂' : X₂ ≤ (X:ℝ) := by linarith only [hx₂,Nat.cast_nonneg (α:=ℝ) X]
  have G := hbound A X h K δ hA hx₁ hh hlow hhX hδ hδX hAX hs₁ hs₂ hlog
  dsimp only at G ⊢
  have hz (Y : ℝ) (hY : X₂ ≤ Y) :
      zeroFamilyEnergy (analyticPrimitiveFamily A)
        (fun χ => rightBadIndices χ ((2:ℝ)^(K+1)) (1-V1l.V2j (B+4) Y)) Y h = 0 := by
    unfold zeroFamilyEnergy
    apply sum_eq_zero
    intro χ _
    dsimp only
    rw [hX₂ Y hY χ ((2:ℝ)^(K+1))]
    simp [zeroWindow]
  rw [hz _ hx₂,hz _ hx₂',add_zero,mul_zero,add_zero] at G
  exact G

end
end InnerFloorResearch
