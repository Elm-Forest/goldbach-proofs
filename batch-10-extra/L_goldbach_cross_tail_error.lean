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
  have hD : |‖a+b‖-‖a‖| ≤ ‖b‖ := by
    rw [abs_le]
    constructor <;> linarith
  have hS : ‖a+b‖+‖a‖ ≤ 2*‖a‖+‖b‖ := by linarith
  rw [show ‖a+b‖^2-‖a‖^2 = (‖a+b‖-‖a‖)*(‖a+b‖+‖a‖) by ring, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ‖a+b‖+‖a‖)]
  calc
    _ ≤ ‖b‖*(2*‖a‖+‖b‖) := mul_le_mul hD hS (by positivity) (norm_nonneg _)
    _ = _ := by ring
