import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
Research auxiliary: the accepted primitive-character zero-density mean-square
estimate applies to the entire fixed-strip part of the zero spectrum on the
inner-arc window scale. This does NOT assert that the remaining zero spectrum
is empty, and does NOT assume or import GRH.
-/

open Finset Filter MeasureTheory
open scoped Interval Topology Classical
open OAI.Ostmann V1l V1e Vg2
namespace InnerFloorResearch
noncomputable section

/-- A fixed strip gap eventually dominates the logarithmic cutoff of the
existing zero-density estimate. -/
theorem fixedStripDominatesCutoff (B : ℕ) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, V2j (B+4) X ≤ (1/8 : ℝ) := by
  have ht : Tendsto (fun X : ℝ => Real.log (Real.log X)/Real.log X)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have h := (tendsto_const_nhds (x := (3 : ℝ)*((B+4+14 : ℕ) : ℝ))).mul ht
  have he := h.eventually (gt_mem_nhds (show
    (3 : ℝ)*((B+4+14 : ℕ) : ℝ)*0 < 1/8 by norm_num))
  have he' : ∀ᶠ X : ℝ in atTop, V2j (B+4) X ≤ (1/8 : ℝ) := by
    filter_upwards [he] with X hX
    have hX' : (3 : ℝ)*((B+4+14 : ℕ) : ℝ)*
        (Real.log (Real.log X)/Real.log X) < 1/8 := by simpa using hX
    unfold V2j
    rw [mul_div_assoc]
    exact hX'.le
  exact eventually_atTop.mp he'

/-- For the dyadic height band, the entire 1/2 <= beta <= 7/8 component
has a log-saving mean square. The family and zero subsets can vary freely. -/
theorem fixedStripWindowBand (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X h T : ℝ,
      X₀≤X → 2≤T → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*T)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ ⊆ ((V1 χ).V14 T).filter (fun i =>
        1/2≤((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re≤7/8 ∧
        T/2≤|((V1 χ).zeros i).im|)) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₁,h₁⟩ := V93.Vz7 B
  obtain ⟨X₂,h₂⟩ := fixedStripDominatesCutoff B
  refine ⟨C,hC,max X₁ X₂,?_⟩
  intro Q hQ X h T hX hT hh hhX hscale hlog F hF S hS
  apply h₁ Q hQ X h T ((le_max_left _ _).trans hX) hT hh hhX
    hscale hlog F hF S
  intro χ hχ i hi
  obtain ⟨hiT,hiR,hiB,hiH⟩ := mem_filter.mp (hS χ hχ hi)
  have hc := h₂ X ((le_max_right _ _).trans hX)
  unfold Vy2
  exact mem_filter.mpr ⟨hiT,hiR,by linarith,hiH⟩

/-- At height <= 2, the same estimate holds, without a lower-height
restriction. -/
theorem fixedStripWindowLow (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ,
      ∀ (Q : ℕ), 1≤Q → ∀ X h : ℝ,
      X₀≤X → 0<h → h≤X →
      (Q : ℝ)^2/(h/X)≤X^(5/12 : ℝ) →
      Real.log ((Q : ℝ)*2)≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter,
      (∀ χ∈F, χ.modulus≤Q) →
      ∀ S : PrimitiveComplexCharacter → Finset ℕ,
      (∀ χ∈F, S χ ⊆ ((V1 χ).V14 2).filter (fun i =>
        1/2≤((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re≤7/8)) →
      (∑ χ∈F, ∫ y in X..2*X, ‖∑ i∈S χ,
        Ve y h ((V1 χ).zeros i)‖^2) ≤
        C*h^2*X/(Real.log X)^B := by
  obtain ⟨C,hC,X₁,h₁⟩ := V93.V1ep B
  obtain ⟨X₂,h₂⟩ := fixedStripDominatesCutoff B
  refine ⟨C,hC,max X₁ X₂,?_⟩
  intro Q hQ X h hX hh hhX hscale hlog F hF S hS
  apply h₁ Q hQ X h ((le_max_left _ _).trans hX) hh hhX
    hscale hlog F hF S
  intro χ hχ i hi
  obtain ⟨hiT,hiR,hiB⟩ := mem_filter.mp (hS χ hχ hi)
  have hc := h₂ X ((le_max_right _ _).trans hX)
  exact mem_filter.mpr ⟨hiT,hiR,by linarith⟩

end
end InnerFloorResearch
