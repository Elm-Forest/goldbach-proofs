import Conjectures.Goldbach.InnerFloorFullSpectrum

/-!
An explicit adapter for the public Dirichlet L-function nonvanishing
statement. It does not import that theorem and does not assert it.
The proof needs an approved unconditional theorem of this exact type
(or a weaker uniform positive strip gap). No new axioms are introduced.
-/
open Finset Filter MeasureTheory
open scoped Classical Interval Topology
open OAI.Ostmann V1e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def DirichletUniformStrip (σ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    σ < s.re → ¬(χ=1 ∧ s=1) → DirichletCharacter.LFunction χ s ≠ 0

theorem uniformStrip_enumeratedGap {σ : ℝ} (hs : DirichletUniformStrip σ) :
    ∀ (χ : PrimitiveComplexCharacter) (i : ℕ),
      ((V1 χ).zeros i).re ≤ σ := by
  intro χ i
  by_contra! hi
  letI : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact hs χ.modulus χ.character ((V1 χ).zeros i) hi
    (fun h => χ.nontrivial h.1) ((V1 χ).actual_zero i)

theorem fullSpectrumEnergy_of_uniformStrip {σ : ℝ} (hσ : σ < 1)
    (hs : DirichletUniformStrip σ) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 2≤X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ), 1≤Q → X₀≤X → 0 < h → h≤X →
      (Q:ℝ)^2/(h/X)≤X^(5/12:ℝ) →
      Real.log ((Q:ℝ)*(2:ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ∈F,χ.modulus≤Q) →
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 ((2:ℝ)^(K+1))) X h ≤
        C*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₁,hX₁,hbound⟩ := fullSpectrumEnergyWithResidual B
  obtain ⟨X₂,hX₂⟩ := eventually_atTop.mp
    (eventually_badIndices_empty_of_uniform_gap (B+4) σ hσ
      (uniformStrip_enumeratedGap hs))
  refine ⟨C,hC,max X₁ X₂,hX₁.trans (le_max_left ..),?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF
  have hb := hbound Q K X h hQ ((le_max_left X₁ X₂).trans hX)
    hh hhX hscale hlog F hF
  dsimp only at hb
  have hz : zeroFamilyEnergy F
      (fun χ => rightBadIndices χ ((2:ℝ)^(K+1)) (1-V1l.V2j (B+4) X)) X h = 0 := by
    unfold zeroFamilyEnergy
    apply sum_eq_zero
    intro χ _
    rw [hX₂ X ((le_max_right X₁ X₂).trans hX) χ ((2:ℝ)^(K+1))]
    simp [zeroWindow]
  rw [hz,mul_zero,add_zero] at hb
  exact hb

end
end InnerFloorResearch
