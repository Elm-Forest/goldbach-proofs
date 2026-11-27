import Conjectures.Goldbach.InnerFloorFixedBandAnalyticParameters

/-! All exact hypotheses of the primitive spectral block theorem from
the fixed exponent band parameters. Global smoothing delta=n^(2/3)
and dyadic truncation U~n^(3/2) work simultaneously for 2h<=X<=n. -/
open Filter Finset
open scoped Classical Topology
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 2000000

private theorem power_reserve {n e c d R : ℝ} (hn : 1 ≤ n)
    (hR : 0 ≤ R) (hsmall : R ≤ n^d) (he : e+d ≤ c) :
    R*n^e ≤ n^c := by
  have hnp : 0 < n := by linarith
  calc
    _ ≤ n^d*n^e := mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hnp.le _)
    _ = n^(d+e) := (Real.rpow_add hnp d e).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (by linarith)

theorem eventualFixedBlockScale :
    ∀ᶠ n : ℕ in atTop, ∀ j < 10, ∀ X : ℕ,
      let A := fixedBandEnd n (j+1)
      let h := fixedBandWindow n j
      let K := fixedTruncationIndex n
      let δ := (n:ℝ)^(2/3:ℝ)
      2*h ≤ X → X ≤ n →
      1 ≤ A ∧ 0 < h ∧ (2*(X:ℝ))^(4/5:ℝ) ≤ (h:ℝ) ∧
      (h:ℝ) ≤ (X:ℝ)/2 ∧ 1 ≤ δ ∧ δ ≤ (X:ℝ)/2 ∧ A ≤ X ∧
      (A:ℝ)^2/((h:ℝ)/((X:ℝ)/2)) ≤ ((X:ℝ)/2)^(5/12:ℝ) ∧
      (A:ℝ)^2/((h:ℝ)/(X:ℝ)) ≤ (X:ℝ)^(5/12:ℝ) ∧
      Real.log ((A:ℝ)*(2:ℝ)^(K+1)) ≤ 2*Real.log ((X:ℝ)/2) ∧
      (4/5:ℝ)*Real.log (n:ℝ) ≤ Real.log ((X:ℝ)/2) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop, (8:ℝ) ≤ (n:ℝ)^(1/150:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/150)).comp ht).eventually
      (eventually_ge_atTop 8)
  filter_upwards [eventually_ge_atTop (2:ℕ), eventualFixedBandWindows,
    eventualFixedBandPowerEndpoints,hsmall] with n hn hw he hp
  intro j hj X
  dsimp only
  intro hhX hXn
  let A := fixedBandEnd n (j+1)
  let h := fixedBandWindow n j
  let K := fixedTruncationIndex n
  let a := fixedBandUpperExp j
  let c := fixedBandWindowExp j
  let δ := (n:ℝ)^(2/3:ℝ)
  let U := (2:ℝ)^(K+1)
  obtain ⟨hA,hAp,hcp⟩ := he j hj
  obtain ⟨hhlo,hhhi,hwidth⟩ := hw j hj
  obtain ⟨ha,ha',hc,hdens,hUexp,hδexp,hneg,hcub,hpp⟩ := fixedBandGlobalExponents j hj
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnP : (0:ℝ) < n := by linarith
  have hA0 : (0:ℝ) < A := by exact_mod_cast (show 0 < fixedBandEnd n (j+1) by omega)
  have hhP : (0:ℝ) < h :=
    (Real.rpow_pos_of_pos hnP (4/5:ℝ)).trans_le hhlo
  have hhN : 0 < h := Nat.cast_pos.mp hhP
  have hhX' : (h:ℝ) ≤ (X:ℝ)/2 := by
    have H : (2:ℝ)*(h:ℝ) ≤ X := by exact_mod_cast hhX
    linarith only [H]
  have hXP : (0:ℝ) < X := by linarith only [hhP,hhX']
  have hXn' : (X:ℝ) ≤ n := by exact_mod_cast hXn
  have hh1 : 1 ≤ (h:ℝ) := (Real.one_le_rpow hnR (by norm_num : (0:ℝ) ≤ 4/5)).trans hhlo
  have hXhalf1 : 1 ≤ (X:ℝ)/2 := hh1.trans hhX'
  have hp' : (8:ℝ) ≤ (n:ℝ)^(1/100:ℝ) :=
    hp.trans (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num))
  have hlarge : 4*(n:ℝ)^(4/5:ℝ) ≤ (n:ℝ)^c :=
    power_reserve hnR (by norm_num) (by linarith : (4:ℝ) ≤ (n:ℝ)^(1/100:ℝ))
      (by exact hc)
  have hh4 : 2*(n:ℝ)^(4/5:ℝ) ≤ (h:ℝ) := by linarith only [hlarge,hcp]
  have hlow : (2*(X:ℝ))^(4/5:ℝ) ≤ (h:ℝ) := by
    calc
      _ ≤ (2*(n:ℝ))^(4/5:ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ = (2:ℝ)^(4/5:ℝ)*(n:ℝ)^(4/5:ℝ) := Real.mul_rpow (by norm_num) hnP.le
      _ ≤ 2*(n:ℝ)^(4/5:ℝ) :=
        mul_le_mul_of_nonneg_right
          (by simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (4/5:ℝ) ≤ 1))
          (Real.rpow_nonneg hnP.le _)
      _ ≤ _ := hh4
  have hδ1 : 1 ≤ δ := Real.one_le_rpow hnR (by norm_num)
  have hδh : δ ≤ (h:ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (2/3:ℝ) ≤ 4/5)).trans hhlo
  have hAX : (A:ℝ) ≤ X := calc
    _ ≤ (n:ℝ)^a := hAp
    _ ≤ (n:ℝ)^(4/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hnR (by linarith only [ha'])
    _ ≤ h := hhlo
    _ ≤ _ := by linarith only [hhX',hhP]
  have hds (Y : ℝ) (hY : 0 < Y) (hYn : Y ≤ n) :
      (A:ℝ)^2/((h:ℝ)/Y) ≤ Y^(5/12:ℝ) := by
    have hprod : (A:ℝ)^2*Y^(7/12:ℝ) ≤ (h:ℝ) := by
      calc
        _ ≤ ((n:ℝ)^a)^2*(n:ℝ)^(7/12:ℝ) :=
          mul_le_mul (pow_le_pow_left₀ hA0.le hAp 2)
            (Real.rpow_le_rpow hY.le hYn (by norm_num))
            (Real.rpow_nonneg hY.le _) (sq_nonneg _)
        _ = (n:ℝ)^(2*a+7/12) := by
          rw [pow_two,← Real.rpow_add hnP,← Real.rpow_add hnP]
          congr 1 <;> ring
        _ ≤ (h:ℝ) := by
          have H : 2*(n:ℝ)^(2*a+7/12) ≤ (n:ℝ)^c :=
            power_reserve hnR (by norm_num) (by linarith : (2:ℝ) ≤ (n:ℝ)^(1/150:ℝ))
              (by linarith only [hdens])
          linarith only [H,hcp]
    apply (div_le_iff₀ (div_pos hhP hY)).2
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hY).2
    have H := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hY.le (5/12:ℝ))
    rw [mul_assoc,← Real.rpow_add hY,show (7/12:ℝ)+5/12=1 by norm_num,Real.rpow_one] at H
    simpa only [mul_div_assoc,mul_comm,mul_left_comm] using H
  have hUcap : U ≤ 2*(n:ℝ)^(3/2:ℝ) := (fixedTruncation_bounds n (by omega)).2
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hproduct : (A:ℝ)*U ≤ ((X:ℝ)/2)^2 := by
    have hreserve : 8*(n:ℝ)^(a+3/2) ≤ (n:ℝ)^(2*c) :=
      power_reserve hnR (by norm_num)
        (hp.trans (Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (1/150:ℝ) ≤ 1/10)))
        (by linarith only [hUexp])
    have hsq := pow_le_pow_left₀ (Real.rpow_nonneg hnP.le c) hcp 2
    rw [pow_two,← Real.rpow_add hnP,show c+c=2*c by ring] at hsq
    have hsq' : (n:ℝ)^(2*c) ≤ 4*(h:ℝ)^2 := by nlinarith only [hsq]
    calc
      _ ≤ (n:ℝ)^a*(2*(n:ℝ)^(3/2:ℝ)) :=
        mul_le_mul hAp hUcap hUpos.le (Real.rpow_nonneg hnP.le a)
      _ = 2*(n:ℝ)^(a+3/2) := by rw [← mul_assoc,mul_comm ((n:ℝ)^a) 2,mul_assoc,← Real.rpow_add hnP]
      _ ≤ (h:ℝ)^2 := by linarith only [hreserve,hsq']
      _ ≤ _ := pow_le_pow_left₀ hhP.le hhX' 2
  have hlog := Real.log_le_log (mul_pos hA0 hUpos) hproduct
  rw [Real.log_pow] at hlog
  have hloglow := Real.log_le_log (Real.rpow_pos_of_pos hnP (4/5:ℝ)) (hhlo.trans hhX')
  rw [Real.log_rpow hnP] at hloglow
  refine ⟨hA,hhN,hlow,hhX',hδ1,hδh.trans hhX',Nat.cast_le.mp hAX,
    hds ((X:ℝ)/2) (by linarith) (by linarith only [hXn',hXP]),
    hds X hXP hXn',?_,hloglow⟩
  simpa only [Nat.cast_ofNat,U,K,A] using hlog

end
end InnerFloorResearch
