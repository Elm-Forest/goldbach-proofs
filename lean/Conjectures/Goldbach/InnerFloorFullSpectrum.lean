import Conjectures.Goldbach.InnerFloorGoodZeroAssembly
import Conjectures.Goldbach.InnerFloorWindowFormulaEnergy

/-!
Full-spectrum energy with an explicitly retained near-one term.
No fixed zero-free strip is assumed or asserted.
-/
open Finset MeasureTheory Filter
open scoped Classical Interval Topology
open OAI.Ostmann V1e V6b V6i V7e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

def leftIndices (χ : PrimitiveComplexCharacter) (U : ℝ) : Finset ℕ :=
  ((V1 χ).V14 U).filter fun i => ((V1 χ).zeros i).re ≤ 1/2

def rightGoodIndices (χ : PrimitiveComplexCharacter) (U c : ℝ) : Finset ℕ :=
  ((V1 χ).V14 U).filter fun i => 1/2 < ((V1 χ).zeros i).re ∧ ((V1 χ).zeros i).re ≤ c

def rightBadIndices (χ : PrimitiveComplexCharacter) (U c : ℝ) : Finset ℕ :=
  ((V1 χ).V14 U).filter fun i => 1/2 < ((V1 χ).zeros i).re ∧ c < ((V1 χ).zeros i).re

theorem zeroWindow_partition (χ : PrimitiveComplexCharacter) (U c h y : ℝ) :
    zeroWindow χ ((V1 χ).V14 U) h y =
      zeroWindow χ (leftIndices χ U) h y +
      zeroWindow χ (rightGoodIndices χ U c) h y +
      zeroWindow χ (rightBadIndices χ U c) h y := by
  classical
  unfold zeroWindow leftIndices rightGoodIndices rightBadIndices
  simp only [sum_filter]
  rw [← sum_add_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  by_cases hl : ((V1 χ).zeros i).re ≤ 1/2
  · simp [hl,not_lt_of_ge hl]
  · have hr := lt_of_not_ge hl
    by_cases hg : ((V1 χ).zeros i).re ≤ c
    · simp [hl,hr,hg,not_lt_of_ge hg]
    · simp [hl,hr,hg,lt_of_not_ge hg]

def zeroFamilyEnergy (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) (X h : ℝ) : ℝ :=
  ∑ χ∈F, ∫ y in X..2*X, ‖zeroWindow χ (S χ) h y‖^2

theorem zeroFamilyEnergy_nonneg (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ) {X h : ℝ} (hX : 0≤X) :
    0≤zeroFamilyEnergy F S X h :=
  sum_nonneg fun _ _ => intervalIntegral.integral_nonneg_of_forall (by linarith)
    fun _ => sq_nonneg _

/-- Only the last, near-one spectral term is uncontrolled. The
factor 3 follows from finite Cauchy--Schwarz rather than cancellation. -/
theorem fullSpectrumSplit (F : Finset PrimitiveComplexCharacter)
    (U c X h : ℝ) (hX : 0<X) (hh : 0≤h) (hhX : h≤X) :
    zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) X h ≤
      3*(zeroFamilyEnergy F (fun χ => leftIndices χ U) X h +
        zeroFamilyEnergy F (fun χ => rightGoodIndices χ U c) X h +
        zeroFamilyEnergy F (fun χ => rightBadIndices χ U c) X h) := by
  let f (χ : PrimitiveComplexCharacter) (i : ℕ) (y : ℝ) :=
    if i=0 then zeroWindow χ (leftIndices χ U) h y
    else if i=1 then zeroWindow χ (rightGoodIndices χ U c) h y
    else zeroWindow χ (rightBadIndices χ U c) h y
  have hp (χ : PrimitiveComplexCharacter) (y : ℝ) :
      (∑ i∈range 3,f χ i y) = zeroWindow χ ((V1 χ).V14 U) h y := by
    rw [zeroWindow_partition χ U c h y]
    norm_num [f,Finset.sum_range_succ]
  have hi (χ : PrimitiveComplexCharacter) (i : ℕ) :
      IntervalIntegrable (fun y => ‖f χ i y‖^2) volume X (2*X) := by
    unfold f
    split_ifs <;> apply ContinuousOn.intervalIntegrable_of_Icc (by linarith) <;>
      exact (V6e _ (V1 χ).zeros X h hX hh hhX).norm.pow 2
  unfold zeroFamilyEnergy
  rw [← sum_add_distrib,← sum_add_distrib,mul_sum]
  apply sum_le_sum
  intro χ _
  have hs := V1dr (range 3) (f χ) X hX.le (fun i _ => hi χ i)
  simp_rw [hp] at hs
  simpa [f,Finset.sum_range_succ] using hs

/-- Existing zero density bounds close the entire good part, leaving
only the explicitly filtered near-one packet. -/
theorem fullSpectrumEnergyWithResidual (B : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∃ X₀ : ℝ, 2≤X₀ ∧
      ∀ (Q K : ℕ) (X h : ℝ), 1≤Q → X₀≤X → 0<h → h≤X →
      (Q:ℝ)^2/(h/X)≤X^(5/12:ℝ) →
      Real.log ((Q:ℝ)*(2:ℝ)^(K+1))≤2*Real.log X →
      ∀ F : Finset PrimitiveComplexCharacter, (∀ χ∈F,χ.modulus≤Q) →
      let U := (2:ℝ)^(K+1)
      let c := 1-V1l.V2j (B+4) X
      zeroFamilyEnergy F (fun χ => (V1 χ).V14 U) X h ≤
        C*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B +
        3*zeroFamilyEnergy F (fun χ => rightBadIndices χ U c) X h := by
  obtain ⟨C₁,hC₁,X₁,h₁⟩ := V9h.V1jv B
  obtain ⟨C₂,hC₂,X₂,_,h₂⟩ := goodZerosAllHeights B
  refine ⟨3*(C₁+C₂),by positivity,max 2 (max X₁ X₂),le_max_left ..,?_⟩
  intro Q K X h hQ hX hh hhX hscale hlog F hF
  dsimp only
  let U := (2:ℝ)^(K+1)
  let c := 1-V1l.V2j (B+4) X
  have hX1 : X₁≤X := (le_max_left X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hX2 : X₂≤X := (le_max_right X₁ X₂).trans ((le_max_right _ _).trans hX)
  have hXge : 2≤X := (le_max_left _ _).trans hX
  have hXp : 0<X := by linarith
  have hL : 0<Real.log X := Real.log_pos (by linarith)
  have hleft := h₁ Q hQ K X h hX1 hh hhX hscale hlog F hF
    (fun χ => leftIndices χ U)
    (fun χ _ => filter_subset _ _) (fun χ _ i hi => (mem_filter.mp hi).2)
  have hright := h₂ Q K X h hQ hX2 hh hhX hscale hlog F hF
    (fun χ => rightGoodIndices χ U c)
    (fun χ _ => filter_subset _ _)
    (fun χ _ i hi => ⟨(mem_filter.mp hi).2.1.le,(mem_filter.mp hi).2.2⟩)
  have hleft' : zeroFamilyEnergy F (fun χ => leftIndices χ U) X h ≤
      C₁*h^2*X/(Real.log X)^B := hleft
  have hright' : zeroFamilyEnergy F (fun χ => rightGoodIndices χ U c) X h ≤
      C₂*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B := hright
  have hk : (1:ℝ)≤((K+1:ℕ):ℝ) := by exact_mod_cast (show 1≤K+1 by omega)
  have hleft'' : zeroFamilyEnergy F (fun χ => leftIndices χ U) X h ≤
      C₁*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B := by
    apply hleft'.trans
    gcongr
    nlinarith
  calc
    _ ≤ _ := fullSpectrumSplit F U c X h hXp hh.le hhX
    _ ≤ 3*(C₁*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B +
      C₂*((K+1:ℕ):ℝ)^2*h^2*X/(Real.log X)^B +
      zeroFamilyEnergy F (fun χ => rightBadIndices χ U c) X h) :=
      mul_le_mul_of_nonneg_left (add_le_add_right (add_le_add hleft'' hright') _)
        (by norm_num)
    _ = _ := by ring

end
end InnerFloorResearch
