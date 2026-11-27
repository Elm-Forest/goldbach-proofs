import Conjectures.Goldbach.InnerFloorUniformBlockLogEight
import Conjectures.Goldbach.InnerFloorFixedBandBoundaryAsymptotic
import Conjectures.Goldbach.InnerFloorBlockSummation

/-!
End-to-end conditional reduction from a uniform Dirichlet zero-free strip.
It is not an unconditional theorem and must not be submitted as one.
-/
open Filter Finset InnerFloorLinearTotient
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 3000000

theorem middleCellEnergySmall_of_uniformStrip {σ : ℝ} (hσ : σ < 1)
    (hs : DirichletUniformStrip σ) : MiddleCellEnergySmall := by
  obtain ⟨M,hM,hblock⟩ := uniformStrip_fixedBandBlockLogEight hσ hs
  have hW := weightConstant_nonneg
  let W := weightConstant
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hloglarge : ∀ᶠ n : ℕ in atTop,
      max 1 (80*M*W^2) ≤ Real.log (n:ℝ) :=
    (Real.tendsto_log_atTop.comp ht).eventually
      (eventually_ge_atTop (max 1 (80*M*W^2)))
  have hpower : ∀ᶠ n : ℕ in atTop, (3:ℝ) ≤ (n:ℝ)^(1/100:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/100)).comp ht).eventually
      (eventually_ge_atTop 3)
  unfold MiddleCellEnergySmall
  filter_upwards [eventualInnerGeometry,eventualFixedBandWindows,
    eventualFixedBandPowerEndpoints,hblock,hloglarge,hpower,
    eventualFixedBandBoundarySmall 4 (2/5) (by norm_num)]
    with n hg hw he hb hlog hp hboundary
  obtain ⟨hn,hQ,hQA,hAB,huH,hsep⟩ := hg
  let L := Real.log (n:ℝ)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnP : (0:ℝ) < n := by linarith
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlog
  have hL : 0 < L := by linarith
  have hLbudget : 80*M*W^2 ≤ L^2 := by
    have H := (le_max_right 1 (80*M*W^2)).trans hlog
    have HL : L ≤ L^2 := by nlinarith only [hL1,sq_nonneg (L-1)]
    exact H.trans HL
  have hu0 : 0 ≤ innerWidth n := by unfold innerWidth; positivity
  have hB1 : (1:ℝ) ≤ outerCutoff n := by
    exact_mod_cast hQ.trans (hQA.trans hAB)
  have huN : innerWidth n ≤ (n:ℝ) := by
    have huH0 : (0:ℝ) ≤ GoldbachGRHBudget.width n := Nat.cast_nonneg _
    have H := mul_le_mul_of_nonneg_right hB1 huH0
    nlinarith only [H,huH,hsep,huH0]
  have hbands : ∀ j < 10,
      mediumCellEnergy n (fixedBandEnd n j) (fixedBandEnd n (j+1)) (innerWidth n) ≤
        (4/5:ℝ)*(n:ℝ)/L^4 := by
    intro j hj
    let D := fixedBandEnd n j
    let A := fixedBandEnd n (j+1)
    let h := fixedBandWindow n j
    obtain ⟨hhlo,hhcap,hwidth⟩ := hw j hj
    obtain ⟨hA,hAp,_⟩ := he j hj
    have ha : fixedBandUpperExp j ≤ 1/5 := (fixedBandGlobalExponents j hj).2.1
    have hA0 : 0 < A := by omega
    have hD1 : 1 ≤ D := hQ.trans (le_max_left _ _)
    have hhR : (0:ℝ) < h :=
      (Real.rpow_pos_of_pos hnP (4/5:ℝ)).trans_le hhlo
    have hhN : 0 < h := Nat.cast_pos.mp hhR
    have hAupper : (A:ℝ) ≤ (n:ℝ)^(1/5:ℝ) :=
      hAp.trans (Real.rpow_le_rpow_of_exponent_le hnR ha)
    have hA2 : (A:ℝ)^2 ≤ (h:ℝ) := by
      calc
        _ ≤ ((n:ℝ)^(1/5:ℝ))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hAupper 2
        _ = (n:ℝ)^(2/5:ℝ) := by rw [pow_two,← Real.rpow_add hnP]; norm_num
        _ ≤ (n:ℝ)^(4/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
        _ ≤ _ := hhlo
    have hAh : A ≤ h := Nat.cast_le.mp
      (hAupper.trans ((Real.rpow_le_rpow_of_exponent_le hnR
        (by norm_num : (1/5:ℝ) ≤ 4/5)).trans hhlo))
    have h3h : 3*h ≤ n := by
      apply Nat.cast_le.mp
      push_cast
      calc
        _ ≤ 3*(n:ℝ)^(99/100:ℝ) := mul_le_mul_of_nonneg_left hhcap (by norm_num)
        _ ≤ (n:ℝ)^(1/100:ℝ)*(n:ℝ)^(99/100:ℝ) :=
          mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hnP.le _)
        _ = _ := by rw [← Real.rpow_add hnP]; norm_num
    have hAn : A ≤ n := by omega
    let N := n+1-h
    have hN : N ≤ n := by dsimp [N]; omega
    let f (y : ℕ) := ∑ d∈Icc 1 A,primitivePrimeWindowEnergy d y h
    have hf (y : ℕ) : 0 ≤ f y := by
      unfold f primitivePrimeWindowEnergy
      exact sum_nonneg fun d _ => sum_nonneg fun χ _ => sq_nonneg _
    have hbulk : (∑ y∈Ico (2*h) N,f y) ≤
        2*(M*(h:ℝ)^2/L^8)*(N:ℝ) := by
      apply positiveBlockSum_le f hf (2*h) N (by omega)
        (M*(h:ℝ)^2/L^8) (by positivity)
      intro Z hZ hZN
      have H := hb j hj Z hZ (hZN.trans hN)
      simpa only [f,div_mul_eq_mul_div] using H
    have hlogA : Real.log (A:ℝ) ≤ L :=
      Real.log_le_log (by exact_mod_cast hA0) (by exact_mod_cast hAn)
    have hlogA0 : 0 ≤ Real.log (A:ℝ) := Real.log_nonneg (by exact_mod_cast hA)
    have hwcoef : (W*(1+Real.log (A:ℝ)))^2 ≤ 4*W^2*L^2 := by
      have H : W*(1+Real.log (A:ℝ)) ≤ 2*W*L := by
        have hh := mul_le_mul_of_nonneg_left (show 1+Real.log (A:ℝ) ≤ 2*L by linarith) hW
        nlinarith only [hh]
      calc
        _ ≤ (2*W*L)^2 := pow_le_pow_left₀ (by positivity) H 2
        _ = _ := by ring
    have hbulkN : (∑ y∈Ico (2*h) N,f y) ≤ 2*(M*(h:ℝ)^2/L^8)*(n:ℝ) :=
      hbulk.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hN) (by positivity))
    have hbulkSmall :
        4*(W*(1+Real.log (A:ℝ)))^2*(∑ y∈Ico (2*h) N,f y)/(h:ℝ)^2 ≤
          (2/5:ℝ)*(n:ℝ)/L^4 := by
      have hS : 0 ≤ ∑ y∈Ico (2*h) N,f y := sum_nonneg fun y _ => hf y
      calc
        _ ≤ 4*(4*W^2*L^2)*(2*(M*(h:ℝ)^2/L^8)*(n:ℝ))/(h:ℝ)^2 := by
          gcongr
        _ = (32*M*W^2/L^2)*(n:ℝ)/L^4 := by field_simp; ring
        _ ≤ _ := by
          have H : 32*M*W^2/L^2 ≤ (2/5:ℝ) := by
            apply (div_le_iff₀ (sq_pos_of_pos hL)).2
            linarith only [hLbudget]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right H hnP.le) (by positivity)
    have hbd := hboundary A h hA (by omega) hhN hA2 hhcap
    have hcell := bandCellEnergy_le_bulkBoundary (n:=n) (D:=D) (A:=A)
      (h:=h) (X:=2*h) (u:=innerWidth n) (by omega) hD1 hA0 hhN
      hu0 huN hwidth (by omega) (by omega)
    change (h:ℝ)^2*mediumCellEnergy n D A (innerWidth n) ≤
      4*((W*(1+Real.log (A:ℝ)))^2*(∑ y∈Ico (2*h) N,f y)+
      ((2*h+2*h:ℕ):ℝ)*boundaryWindowBudget A n h) at hcell
    -- Normalize the cell inequality by h² without dropping either term.
    have hnorm : mediumCellEnergy n D A (innerWidth n) ≤
        4*(W*(1+Real.log (A:ℝ)))^2*(∑ y∈Ico (2*h) N,f y)/(h:ℝ)^2+
        4*((2*h+2*h:ℕ):ℝ)*boundaryWindowBudget A n h/(h:ℝ)^2 := by
      calc
        _ ≤ 4*((W*(1+Real.log (A:ℝ)))^2*(∑ y∈Ico (2*h) N,f y)+
            ((2*h+2*h:ℕ):ℝ)*boundaryWindowBudget A n h)/(h:ℝ)^2 :=
          (le_div_iff₀ (sq_pos_of_pos hhR)).2 (by simpa only [mul_comm] using hcell)
        _ = _ := by ring
    exact hnorm.trans (by linarith only [hbulkSmall,hbd])
  have H := mediumCellEnergy_of_fixed_bounds n (innerWidth n)
    ((4/5:ℝ)*(n:ℝ)/L^4) (by omega) hQ hQA hbands
  exact H.trans_eq (by ring)

theorem frozenWideRemainderInnerFloor_of_uniformStrip {σ : ℝ}
    (hσ : σ < 1) (hs : DirichletUniformStrip σ) : FrozenWideRemainderInnerFloor :=
  candidate_of_middleCellEnergy (middleCellEnergySmall_of_uniformStrip hσ hs)

end
end InnerFloorResearch
