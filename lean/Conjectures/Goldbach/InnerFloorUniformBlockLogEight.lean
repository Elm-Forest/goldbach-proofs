import Conjectures.Goldbach.InnerFloorUniformStripArithmetic
import Conjectures.Goldbach.InnerFloorFixedBlockScale
import Conjectures.Goldbach.InnerFloorGlobalSmoothingBudget
import Conjectures.Goldbach.InnerFloorBlockScalarBudget

/-! Conditional uniform arithmetic block theorem. All scale choices
and logarithmic losses are explicit. The only unproved hypothesis is
DirichletUniformStrip σ, σ<1. -/
open Filter Finset OAI.Ostmann
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

theorem uniformStrip_fixedBandBlockLogEight {σ : ℝ} (hσ : σ < 1)
    (hs : DirichletUniformStrip σ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j < 10, ∀ X : ℕ,
      let A := fixedBandEnd n (j+1)
      let h := fixedBandWindow n j
      2*h ≤ X → X ≤ n →
      (∑ y∈Ico X (2*X),∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h) ≤
        M*(h:ℝ)^2*(X:ℝ)/(Real.log n)^8 := by
  obtain ⟨D,C,P,hD,hC,hP,X₀,hX₀,hbound⟩ :=
    actualPrimitiveBlockOfUniformStrip hσ hs 10
  let M := 2*(8*D+16)^2+76800*C+256*P
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M,hM,?_⟩
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbig : ∀ᶠ n : ℕ in atTop, X₀ ≤ (n:ℝ)^(4/5:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 4/5)).comp ht).eventually
      (eventually_ge_atTop X₀)
  filter_upwards [eventually_ge_atTop (4:ℕ),eventualFixedBandWindows,
    eventualFixedBandPowerEndpoints,eventualFixedBlockScale,hbig,
    GoldbachGRHBudget.eventually_log_pow_le 10 (1/5) 1 (by norm_num) (by norm_num)]
    with n hn hw hp hscale hbig hsmall
  intro j hj X
  dsimp only
  intro hhX hXn
  let A := fixedBandEnd n (j+1)
  let h := fixedBandWindow n j
  let K := fixedTruncationIndex n
  let δ := (n:ℝ)^(2/3:ℝ)
  let U := (2:ℝ)^(K+1)
  let E := D*(δ*Real.log X+Real.sqrt X*Real.log X/δ+
        (A:ℝ)^2*(X:ℝ)^2*Real.log ((A:ℝ)*U)/(δ*U))+
          2*Real.sqrt (3*(X:ℝ))*Real.log (3*(X:ℝ))
  obtain ⟨hA,hh,hlow,hhX',hδ1,hδX,hAX,hds₁,hds₂,hlog,hloglow⟩ :=
    hscale j hj X hhX hXn
  obtain ⟨_,hAp,hcp⟩ := hp j hj
  obtain ⟨hhlo,_,_⟩ := hw j hj
  obtain ⟨_,_,_,_,_,he₁,he₂,he₃,he₄⟩ := fixedBandGlobalExponents j hj
  have hnR : (3:ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have hnP : (0:ℝ) < n := by linarith
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hX0' : X₀ ≤ (X:ℝ) := by
    have H := hbig.trans hhlo
    linarith only [H,hhX',hhR]
  have hX1 : (1:ℝ) ≤ X := by linarith
  have hXn' : (X:ℝ) ≤ n := by exact_mod_cast hXn
  have hA1 : (1:ℝ) ≤ A := by exact_mod_cast hA
  have hUlo : (n:ℝ)^(3/2:ℝ) ≤ U := (fixedTruncation_bounds n (by omega)).1
  have hU1 : 1 ≤ U :=
    (Real.one_le_rpow (by linarith : (1:ℝ) ≤ n) (by norm_num)).trans hUlo
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith)
  have hLhalf : Real.log (n:ℝ)/2 ≤ Real.log ((X:ℝ)/2) := by linarith
  have hLhalfpos : 0 < (X:ℝ)/2 := by linarith only [hhR,hhX']
  have hLhalf_le : Real.log ((X:ℝ)/2) ≤ Real.log (n:ℝ) :=
    Real.log_le_log hLhalfpos (by linarith)
  have hLfull : Real.log (n:ℝ)/2 ≤ Real.log (X:ℝ) :=
    hLhalf.trans (Real.log_le_log hLhalfpos (by linarith))
  have hlog' : Real.log ((A:ℝ)*U) ≤ 2*Real.log n := by
    linarith only [hlog,hLhalf_le]
  have hLx : 0 ≤ Real.log (X:ℝ) := Real.log_nonneg hX1
  have hL3 : 0 ≤ Real.log (3*(X:ℝ)) := Real.log_nonneg (by linarith)
  have hLAU : 0 ≤ Real.log ((A:ℝ)*U) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hA1 hU1)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have herror : (A:ℝ)*E ≤ (8*D+16)*(h:ℝ)*(n:ℝ)^(-(1/10):ℝ)*Real.log n :=
    globalSmoothingBudget hnR hX1 hXn' hA1 hhR hD hAp hcp hUlo hlog'
      he₁ he₂ he₃ he₄
  have hscalar := blockScalarBudget
    (show (1:ℝ) ≤ n by linarith) (Nat.cast_nonneg (α:=ℝ) X)
    (Nat.cast_nonneg (α:=ℝ) A) hhR.le hE
    (Nat.cast_nonneg (α:=ℝ) (K+1)) hD.le hC.le hP.le hL hLhalf hLfull
    (fixedTruncation_logBound n (by omega)) herror (by simpa only [one_mul] using hsmall)
  have H := hbound A X h K δ hA hX0' hh hlow hhX' hδ1 hδX hAX hds₁ hds₂ hlog
  dsimp only at H
  exact H.trans (by simpa only [M,E,δ,U,K,A,h] using hscalar)

end
end InnerFloorResearch
