import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_cross_tail_error :
    ∀ a b : ℂ, |‖a+b‖^2-‖a‖^2| ≤ 2*‖a‖*‖b‖+‖b‖^2 := by
  intro a b
  have h1 : ‖a+b‖ ≤ ‖a‖+‖b‖ := norm_add_le _ _
  have h2 : ‖a‖ ≤ ‖a+b‖+‖b‖ := by
    calc
      ‖a‖ = ‖(a+b)-b‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖a+b‖+‖b‖ := norm_sub_le _ _
  have h3 : ‖a+b‖^2 ≤ (‖a‖+‖b‖)^2 := by
    gcongr
  have h4 : ‖a‖^2 ≤ (‖a+b‖+‖b‖)^2 := by
    gcongr
  rw [abs_le]
  constructor
  · have h5 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ 2*‖b‖ by positivity)
    nlinarith
  · nlinarith
