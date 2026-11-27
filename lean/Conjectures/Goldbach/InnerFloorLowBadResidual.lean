import Conjectures.Goldbach.InnerFloorFullSpectrum
import Conjectures.Goldbach.InnerFloorHighBadZeros

/-!
The residual is restricted to low-height near-one zeros. Above the
cutoff T = O(X/h times a power of log X), sparse counting and
oscillatory window decay suffice without any zero-free hypothesis.
-/
open Finset MeasureTheory
open scoped Classical Interval
open OAI.Ostmann V1e V6b V6i V7e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def lowHeightBad (χ : PrimitiveComplexCharacter) (U c T : ℝ) : Finset ℕ :=
  (rightBadIndices χ U c).filter (fun i => |((V1 χ).zeros i).im| < T)

def highHeightBad (χ : PrimitiveComplexCharacter) (U c T : ℝ) : Finset ℕ :=
  (rightBadIndices χ U c).filter (fun i => T ≤ |((V1 χ).zeros i).im|)

theorem badSpectrumHeightSplit
    (F : Finset PrimitiveComplexCharacter) (U c T X h : ℝ)
    (hX : 0 < X) (hh : 0≤h) (hhX : h≤X) :
    zeroFamilyEnergy F (fun χ => rightBadIndices χ U c) X h ≤
      2*(zeroFamilyEnergy F (fun χ => lowHeightBad χ U c T) X h+
        zeroFamilyEnergy F (fun χ => highHeightBad χ U c T) X h) := by
  let f (χ : PrimitiveComplexCharacter) (i : ℕ) (y : ℝ) :=
    if i=0 then zeroWindow χ (lowHeightBad χ U c T) h y
    else zeroWindow χ (highHeightBad χ U c T) h y
  have hp (χ : PrimitiveComplexCharacter) (y : ℝ) :
      (∑ i∈range 2,f χ i y) = zeroWindow χ (rightBadIndices χ U c) h y := by
    norm_num [f,Finset.sum_range_succ]
    unfold zeroWindow lowHeightBad highHeightBad
    simpa only [not_lt] using (Finset.sum_filter_add_sum_filter_not
      (rightBadIndices χ U c) (fun i => |((V1 χ).zeros i).im| < T)
      (fun i => Ve y h ((V1 χ).zeros i))).symm
  have hi (χ : PrimitiveComplexCharacter) (i : ℕ) :
      IntervalIntegrable (fun y => ‖f χ i y‖^2) volume X (2*X) := by
    unfold f
    split_ifs <;> apply ContinuousOn.intervalIntegrable_of_Icc (by linarith) <;>
      exact (V6e _ (V1 χ).zeros X h hX hh hhX).norm.pow 2
  unfold zeroFamilyEnergy
  rw [← sum_add_distrib,mul_sum]
  apply sum_le_sum
  intro χ _
  have hs := V1dr (range 2) (f χ) X hX.le (fun i _ => hi χ i)
  simp_rw [hp] at hs
  simpa [f,Finset.sum_range_succ] using hs

/-- The high-height bad packet is bounded unconditionally, provided
the explicit polylogarithmic height reserve is met. -/
theorem badSpectrumLowResidual (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : ℕ) (X U h T ε : ℝ), 1≤Q → Real.exp 1≤X →
      2≤U → (Q:ℝ)≤X → Real.log ((Q:ℝ)*U)≤2*Real.log X →
      0≤V1l.V2j A X → V1l.V2j A X≤1/2 →
      0≤h → h≤X → 0 < T → 0≤ε →
      6*X*(C*(Real.log X)^(27*(A+14)+13))≤ε*h*T →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ∈F,χ.modulus≤Q) →
      let c := 1-V1l.V2j A X
      zeroFamilyEnergy F (fun χ => rightBadIndices χ U c) X h ≤
        2*zeroFamilyEnergy F (fun χ => lowHeightBad χ U c T) X h+
        2*ε^2*h^2*X := by
  obtain ⟨C,hC,hcount⟩ := nearOneOccurrencesCard A
  refine ⟨C,hC,?_⟩
  intro Q X U h T ε hQ hX hU hQX hlog hδ hδ' hh hhX hT hε hres F hF
  dsimp only
  let c := 1-V1l.V2j A X
  have hX1 : 1≤X := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hXp : 0 < X := by linarith
  have hL : 0≤Real.log X := Real.log_nonneg hX1
  have hcard :
      (∑ χ∈F, ((highHeightBad χ U c T).card:ℝ))≤
        C*(Real.log X)^(27*(A+14)+13) := by
    apply le_trans _ (hcount Q X U hQ hX hU hQX hlog hδ hδ' F hF)
    apply sum_le_sum
    intro χ _
    apply Nat.cast_le.mpr
    apply card_le_card
    intro i hi
    have hp := mem_filter.mp ((mem_filter.mp hi).1)
    exact mem_filter.mpr ⟨hp.1,hp.2.2⟩
  have hhigh := highZeroFamilyEnergyReserve F
    (fun χ => highHeightBad χ U c T) hX1 hh hhX hT
    (show 0≤C*(Real.log X)^(27*(A+14)+13) by positivity)
    hε hcard (fun χ _ i hi => (mem_filter.mp hi).2) hres
  change zeroFamilyEnergy F (fun χ => highHeightBad χ U c T) X h ≤ ε^2*h^2*X at hhigh
  have hsplit := badSpectrumHeightSplit F U c T X h hXp hh hhX
  linarith only [hsplit,hhigh]

end
end InnerFloorResearch
