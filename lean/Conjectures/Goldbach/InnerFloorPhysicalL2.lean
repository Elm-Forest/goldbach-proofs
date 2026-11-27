import Conjectures.Goldbach.ShortProgressionsMeanTheta

/-!
Research adaptation of the Plancherel and logarithmic coordinate proof in
ShortProgressionsMeanTheta.lean (accepted Goldbach PR #3789, XBribo,
a546c6629fae0223b56067d5e4ebc34043c4fbf1; Apache-2.0).
Keep the physical second moment instead of converting it to L1.
Only regular spectral boxes are covered; exceptional boxes still need proof.
-/

section

noncomputable section

open Finset Set MeasureTheory FourierTransform ShortAPExceptionalAmplitude ShortAPFrequencyAssembly
open scoped SchwartzMap FourierTransform ContDiff BigOperators

namespace InnerFloorResearch.PhysicalL2
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in


private theorem test_fourier_swap {f : ℝ → ℂ} (hf : Integrable f) (g : 𝓢(ℝ, ℂ)) :
    (∫ x, (𝓕 f) x • g x) = ∫ x, f x • (𝓕 g) x := by
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf g.integrable
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem ae_eq_of_schwartz_test {u v : ℝ → ℂ}
    (hu : LocallyIntegrable u volume) (hv : LocallyIntegrable v volume)
    (h : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * u x) = ∫ x, φ x * v x) :
    u =ᵐ[volume] v := by
  apply ae_eq_of_integral_contDiff_smul_eq hu hv
  intro g hg hgc
  let φ := (hgc.comp_left (show Complex.ofRealCLM 0 = 0 by simp)).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) by fun_prop)
  simp only [RCLike.real_smul_eq_coe_mul]
  exact h φ
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem lp_test (v : Lp ℂ 2 (volume : Measure ℝ)) (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, (𝓕 φ) x • v x) = ∫ x, φ x • (𝓕 v) x := calc
  _ = Lp.toTemperedDistribution v (𝓕 φ) := (Lp.toTemperedDistribution_apply ..).symm
  _ = (𝓕 (Lp.toTemperedDistribution v)) φ := rfl
  _ = Lp.toTemperedDistribution (𝓕 v) φ := by rw [Lp.fourier_toTemperedDistribution_eq]
  _ = _ := Lp.toTemperedDistribution_apply ..
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem fourier_agrees {f : ℝ → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (𝓕 f) =ᵐ[volume] (𝓕 (h₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  let v := h₂.toLp f
  have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ h₁
  apply ae_eq_of_schwartz_test hc.locallyIntegrable
    ((Lp.memLp (𝓕 v)).locallyIntegrable (by norm_num))
  intro φ
  have A := test_fourier_swap (f := f) h₁ φ
  have B := lp_test v φ
  simp only [smul_eq_mul] at A B
  have C : (∫ x : ℝ, f x * (𝓕 φ) x) = ∫ x : ℝ, (𝓕 φ) x * v x := by
    apply integral_congr_ae
    filter_upwards [h₂.coeFn_toLp] with x hx
    change f x * (𝓕 φ) x = (𝓕 φ) x * (h₂.toLp f) x
    rw [hx, mul_comm]
  have D : (∫ x : ℝ, φ x * (𝓕 f) x) = ∫ x : ℝ, (𝓕 f) x * φ x :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm ..)
  exact D.trans (A.trans (C.trans B))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem lp_energy (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫ x, ‖f x‖^2 = ‖f‖^2 := by
  conv_rhs => rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)]
  exact integral_congr_ae (ae_of_all _ fun x => norm_sq_eq_re_inner (𝕜 := ℂ) (f x))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem box_plancherel {f : ℝ → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2) :
    Integrable (fun ξ => ‖𝓕 f ξ‖^2) ∧ (∫ ξ, ‖𝓕 f ξ‖^2) = ∫ x, ‖f x‖^2 := by
  let v := h₂.toLp f
  have he := fourier_agrees h₁ h₂
  have hae : (fun ξ => ‖𝓕 f ξ‖^2) =ᵐ[volume] (fun ξ => ‖(𝓕 v) ξ‖^2) := by
    filter_upwards [he] with ξ h using congrArg (fun z : ℂ => ‖z‖^2) h
  refine ⟨((Lp.memLp (𝓕 v)).norm.integrable_sq).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, lp_energy, Lp.norm_fourier_eq, ← lp_energy]
  apply integral_congr_ae
  filter_upwards [h₂.coeFn_toLp] with x h using congrArg (fun z : ℂ => ‖z‖^2) h
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem continuous_window_one {η : ℝ} (hη : 0 ≤ η) :
    Continuous (window η 1) := by
  have hp : Continuous point := by unfold point; fun_prop
  have hn (t : ℝ) : point t ≠ 0 := by
    intro h
    have hr := point_re t
    rw [h, Complex.zero_re] at hr
    norm_num at hr
  have hc : Continuous (fun t : ℝ => (((1+η : ℝ):ℂ)^point t)) :=
    (continuous_const_cpow' (Complex.ofReal_ne_zero.mpr (by linarith))).comp hp
  have hc' : Continuous (fun t : ℝ => ((((1+η : ℝ):ℂ)^point t)-1)/point t) :=
    (hc.sub (continuous_const (y := (1:ℂ)))).div hp hn
  convert hc' using 1
  funext t
  simp only [window, Complex.ofReal_one, Complex.one_cpow, mul_one]
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem cpow_point {y : ℝ} (hy : 0 < y) (t : ℝ) :
    (y:ℂ)^point t = (Real.sqrt y:ℂ) * Complex.exp (((Real.log y*t:ℝ):ℂ)*Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← Complex.ofReal_log hy.le, point, mul_add, Complex.exp_add]
  congr 1
  · rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, Complex.ofReal_exp, Complex.ofReal_mul]
    congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem physical_eq (η : ℝ) {y : ℝ} (hy : 0 < y) (A : ℝ → ℂ) {P : Set ℝ}
    (hP : MeasurableSet P) :
    (∫ t in P, A t * window η y t) = (Real.sqrt y:ℂ) *
      (𝓕 (P.indicator (fun t => A t * window η 1 t))) (-Real.log y/(2*Real.pi)) := by
  rw [← integral_indicator hP, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have ht' : -2 * Real.pi * t * (-Real.log y/(2*Real.pi)) = Real.log y*t := by
    field_simp
  rw [ht']
  by_cases ht : t ∈ P
  · rw [indicator_of_mem ht, indicator_of_mem ht, smul_eq_mul]
    rw [show window η y t = window η 1 t * (y:ℂ)^point t by simp [window], cpow_point hy t]
    ring
  · rw [indicator_of_notMem ht, indicator_of_notMem ht, smul_zero, mul_zero]
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem physical_one_L2 (A : ℝ → ℂ) (hA : Continuous A) {η x T : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1) (hx : 0 < x) (hT : 0 < T) {P : Set ℝ}
    (hP : MeasurableSet P) (hBound : P ⊆ Icc (-(2*T)) (2*T))
    (hBand : ∀ t ∈ P, T ≤ |t|+1) :
    (∫ y in Icc x (4*x), ‖∫ t in P, A t * window η y t‖^2) ≤
      ((4*x)^2*(2*Real.pi)*(18*min η (1/T))^2) *
        (∫ t in P, ‖A t‖^2) := by
  let M := min η (1/T)
  let B := fun t => A t * window η 1 t
  let g := P.indicator B
  let J := Icc (Real.log x) (Real.log (4*x))
  let a := -(2*Real.pi)⁻¹
  let H := fun u => (𝓕 g) (a*u)
  have hBn : Continuous B := hA.mul (continuous_window_one hη)
  have hg₁ : Integrable g := by
    dsimp only [g]
    rw [integrable_indicator_iff hP]
    exact hBn.integrableOn_Icc.mono_set hBound
  have hgMeas : AEStronglyMeasurable g := hg₁.aestronglyMeasurable
  have hgSq : (fun t => ‖g t‖^2) = P.indicator (fun t => ‖B t‖^2) := by
    funext t
    by_cases ht : t ∈ P <;> simp [g, ht]
  have hg₂ : MemLp g 2 := (memLp_two_iff_integrable_sq_norm hgMeas).mpr (by
    rw [hgSq, integrable_indicator_iff hP]
    exact (hBn.norm.pow 2).integrableOn_Icc.mono_set hBound)
  obtain ⟨hFourierInt, hFourierEq⟩ := box_plancherel hg₁ hg₂
  have ha : a ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (by positivity))
  have haInv : |a⁻¹| = 2*Real.pi := by
    simp only [a, inv_neg, inv_inv, abs_neg]
    exact abs_of_nonneg (by positivity)
  have hH : Continuous H := (VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hg₁).comp (continuous_const.mul continuous_id)
  have hH₂ : Integrable (fun u => ‖H u‖^2) := hFourierInt.comp_mul_left' ha
  have hHEq : (∫ u, ‖H u‖^2) = (2*Real.pi)*∫ t in P, ‖B t‖^2 := by
    calc
      _ = |a⁻¹| • ∫ ξ, ‖𝓕 g ξ‖^2 :=
        Measure.integral_comp_mul_left (fun ξ => ‖𝓕 g ξ‖^2) a
      _ = _ := by rw [haInv, smul_eq_mul, hFourierEq, hgSq, integral_indicator hP]
  have hC : ∫ t in P, ‖B t‖^2 ≤ (18*M)^2 * ∫ t in P, ‖A t‖^2 := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on ((hBn.norm.pow 2).integrableOn_Icc.mono_set hBound)
      (((hA.norm.pow 2).const_mul _).integrableOn_Icc.mono_set hBound) hP ?_
    intro t ht
    have hk := window_norm_le hη hη' (by norm_num : (0:ℝ)<1)
      (by norm_num : (1:ℝ) ∈ Set.Icc 1 (4*1)) hT (hBand t ht)
    simp only [Real.sqrt_one, mul_one] at hk
    rw [norm_mul, mul_pow, mul_comm (‖A t‖^2)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hk 2) (sq_nonneg _)
  have hM : 0 ≤ M := le_min hη (by positivity)
  have hNorm (u : ℝ) : ‖∫ t in P, A t * window η (Real.exp u) t‖ =
      Real.sqrt (Real.exp u) * ‖H u‖ := by
    have harg : -u/(2*Real.pi) = a*u := by dsimp only [a]; ring
    rw [physical_eq η (Real.exp_pos _) A hP, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.log_exp, harg]
  have hSub : (∫ y in Icc x (4*x), ‖∫ t in P, A t * window η y t‖^2) =
      ∫ u in J, (Real.exp u)^2 * ‖H u‖^2 := by
    have hImage : Real.exp '' J = Icc x (4*x) := by
      rw [Real.image_exp_Icc, Real.exp_log hx, Real.exp_log (by positivity : 0 < 4*x)]
    rw [← hImage, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
    apply setIntegral_congr_fun measurableSet_Icc
    intro u _
    change |Real.exp u| • ‖∫ t in P, A t * window η (Real.exp u) t‖^2 = _
    rw [abs_of_pos (Real.exp_pos _), smul_eq_mul, hNorm, mul_pow,
      Real.sq_sqrt (Real.exp_pos _).le]
    ring
  rw [hSub]
  calc
    _ ≤ (4*x)^2 * ∫ u in J, ‖H u‖^2 := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (((Real.continuous_exp.pow 2).mul
        (hH.norm.pow 2)).integrableOn_Icc)
        (((hH.norm.pow 2).const_mul _).integrableOn_Icc)
        measurableSet_Icc ?_
      intro u hu
      have hu' : Real.exp u ≤ 4*x := by
        simpa [Real.exp_log (by positivity : 0<4*x)] using Real.exp_le_exp.mpr hu.2
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.exp_pos _).le hu' 2) (sq_nonneg _)
    _ ≤ (4*x)^2 * ∫ u, ‖H u‖^2 :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hH₂
        (ae_of_all _ fun u => sq_nonneg _)) (sq_nonneg _)
    _ = (4*x)^2*((2*Real.pi)*∫ t in P, ‖B t‖^2) := by rw [hHEq]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hC (by positivity : 0 ≤ 2*Real.pi)
      have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg (4*x))
      exact hh'.trans_eq (by dsimp [M]; ring)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem weighted_box_L2 {ι : Type*} (I : Finset ι) (A : ι → ℝ → ℂ)
    (P : ι → Set ℝ) {η x T K : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1) (hx : Real.exp 1 ≤ x) (hT : 0 < T)
    (hK : 0 ≤ K) (hA : ∀ i ∈ I, Continuous (A i))
    (hP : ∀ i ∈ I, MeasurableSet (P i))
    (hBand : ∀ i ∈ I, P i ⊆ frequencyBand T)
    (hE : (∑ i ∈ I, ∫ t in P i, ‖A i t‖^2)*(Real.log x)^77 ≤
      K*(max 1 (η*T))^2*x) :
    (∑ i ∈ I, ∫ y in Icc x (4*x),
      ‖∫ t in P i, A i t * window η y t‖^2)*(Real.log x)^77 ≤
      (10368*Real.pi)*K*η^2*x^3 := by
  let M := min η (1/T)
  let C := (4*x)^2*(2*Real.pi)*(18*M)^2
  have hx0 := (Real.exp_pos 1).trans_le hx
  have hL : 0 ≤ Real.log x := by
    apply Real.log_nonneg
    exact (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)).trans hx
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs : (∑ i ∈ I, ∫ y in Icc x (4*x),
      ‖∫ t in P i, A i t * window η y t‖^2) ≤
      C*(∑ i ∈ I, ∫ t in P i, ‖A i t‖^2) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    apply physical_one_L2 (A i) (hA i hi) hη hη' hx0 hT (hP i hi)
    · intro t ht
      exact abs_le.mp (by linarith [(hBand i hi ht).2] : |t| ≤ 2*T)
    · intro t ht
      exact (hBand i hi ht).1
  calc
    _ ≤ (C*(∑ i ∈ I, ∫ t in P i, ‖A i t‖^2))*(Real.log x)^77 :=
      mul_le_mul_of_nonneg_right hs (pow_nonneg hL _)
    _ = C*((∑ i ∈ I, ∫ t in P i, ‖A i t‖^2)*(Real.log x)^77) := by ring
    _ ≤ C*(K*(max 1 (η*T))^2*x) := mul_le_mul_of_nonneg_left hE hC
    _ = _ := by
      have hm : M*max 1 (η*T) = η := ShortAPPhysicalBandSum.window_weight_cancel hT
      dsimp only [C]
      calc
        _ = (10368*Real.pi)*K*(M*max 1 (η*T))^2*x^3 := by ring
        _ = _ := by rw [hm]

end InnerFloorResearch.PhysicalL2
end
end
