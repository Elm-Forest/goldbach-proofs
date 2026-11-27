import Conjectures.Goldbach.InnerFloorNearOneSparsity

/-!
High-height damping of the sparse bad spectrum. This holds even for zeros
arbitrarily close to 1. The residual low-height near-one contribution is
NOT controlled by this theorem.
-/

open Finset MeasureTheory
open scoped Interval Classical
open OAI.Ostmann V1e
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem highZeroWindowPointwise {X y h T : ℝ} (hX : 1≤X)
    (hy : y∈Set.Icc X (2*X)) (hh : 0≤h) (hhX : h≤X)
    (hT : 0<T) (ρ : ℂ) (hr : ρ.re≤1) (hγ : T≤|ρ.im|) :
    ‖Ve y h ρ‖ ≤ 6*X/T := by
  have hXp : 0<X := by linarith
  have hb (u : ℝ) (hu : X≤u) (hu' : u≤3*X) :
      ‖(u:ℂ)^ρ‖≤3*X := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hXp.trans_le hu)]
    calc
      _ ≤ u^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (hX.trans hu) hr
      _ ≤ _ := by simpa using hu'
  have hy' := hb y hy.1 (by linarith [hy.2])
  have hyh := hb (y+h) (by linarith [hy.1]) (by linarith [hy.2])
  have hn : T≤‖ρ‖ := hγ.trans (Complex.abs_im_le_norm ρ)
  unfold Ve
  rw [norm_div]
  calc
    _ ≤ (‖((y+h:ℝ):ℂ)^ρ‖+‖(y:ℂ)^ρ‖)/‖ρ‖ :=
      div_le_div_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ 6*X/‖ρ‖ := div_le_div_of_nonneg_right (by linarith) (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hT hn

/-- Any finite packet of high zeros has energy bounded by the SQUARE of
its total number of occurrences. This intentionally pays the full count;
the logarithmic sparsity theorem makes the loss harmless above the
new height cutoff. -/
theorem highZeroFamilyEnergy (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ)
    {X h T M : ℝ} (hX : 1≤X) (hh : 0≤h) (hhX : h≤X)
    (hT : 0<T) (hM : 0≤M)
    (hcard : (∑ χ∈F, ((S χ).card:ℝ))≤M)
    (hheight : ∀ χ∈F, ∀ i∈S χ, T≤|((V1 χ).zeros i).im|) :
    (∑ χ∈F, ∫ y in X..2*X,
        ‖∑ i∈S χ, Ve y h ((V1 χ).zeros i)‖^2) ≤
      X*(6*X/T*M)^2 := by
  have hXp : 0<X := by linarith
  apply V9h.Vlk F _ X (6*X/T*M) hXp.le (by positivity)
    (fun χ _ => V6b.V6e (S χ) (V1 χ).zeros X h hXp hh hhX)
  intro y hy
  calc
    _ ≤ ∑ χ∈F, ∑ i∈S χ, ‖Ve y h ((V1 χ).zeros i)‖ :=
      sum_le_sum (fun χ _ => norm_sum_le _ _)
    _ ≤ ∑ χ∈F, ∑ _i∈S χ, 6*X/T :=
      sum_le_sum (fun χ hχ => sum_le_sum (fun i hi =>
        highZeroWindowPointwise hX hy hh hhX hT _ ((V1 χ).in_strip i).2.le
          (hheight χ hχ i hi)))
    _ = (6*X/T)*(∑ χ∈F, ((S χ).card:ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro χ _
      simp only [sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard (by positivity)

/-- A quantitative height cutoff converts count sparsity to mean-square
saving. In particular if M is polylogarithmic, choose T larger than X/h
by the corresponding polylogarithmic factor. -/
theorem highZeroFamilyEnergyReserve
    (F : Finset PrimitiveComplexCharacter)
    (S : PrimitiveComplexCharacter → Finset ℕ)
    {X h T M ε : ℝ} (hX : 1≤X) (hh : 0≤h) (hhX : h≤X)
    (hT : 0<T) (hM : 0≤M) (hε : 0≤ε)
    (hcard : (∑ χ∈F, ((S χ).card:ℝ))≤M)
    (hheight : ∀ χ∈F, ∀ i∈S χ, T≤|((V1 χ).zeros i).im|)
    (hreserve : 6*X*M ≤ ε*h*T) :
    (∑ χ∈F, ∫ y in X..2*X,
        ‖∑ i∈S χ, Ve y h ((V1 χ).zeros i)‖^2) ≤
      ε^2*h^2*X := by
  apply (highZeroFamilyEnergy F S hX hh hhX hT hM hcard hheight).trans
  have h : 6*X/T*M≤ε*h := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hT).2 hreserve
  calc
    _ ≤ X*(ε*h)^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) h 2) (by linarith)
    _ = _ := by ring

end
end InnerFloorResearch
