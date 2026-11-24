import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_integrated_loss :
    ∀ (f g : ℝ → ℝ) (a b D : ℝ), a≤b → Continuous f → Continuous g → (∀ t∈Set.Icc a b, g t-D≤f t) → intervalIntegral g a b MeasureTheory.volume-(b-a)*D ≤ intervalIntegral f a b MeasureTheory.volume := by
  intro f g a b D hab hf hg h
  have hconst : Continuous (fun _ : ℝ => D) := continuous_const
  have hi : intervalIntegral (fun t => g t - D) a b MeasureTheory.volume ≤
      intervalIntegral f a b MeasureTheory.volume :=
    intervalIntegral.integral_mono_on hab
      (hg.sub hconst).intervalIntegrable hf.intervalIntegrable h
  rw [intervalIntegral.integral_sub hg.intervalIntegrable hconst.intervalIntegrable,
      intervalIntegral.integral_const, smul_eq_mul] at hi
  exact hi
