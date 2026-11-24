import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_offset_cost :
    ∀ X h : ℝ, 0≤h → intervalIntegral (fun t : ℝ => (1+X*t)^2) (0:ℝ) h MeasureTheory.volume=h+X*h^2+X^2*h^3/3 := by
  intro X h hh
  let F : ℝ → ℝ := fun t => t + X * t ^ 2 + X ^ 2 * t ^ 3 / 3
  have hd : ∀ t : ℝ, HasDerivAt F ((1 + X * t) ^ 2) t := by
    intro t
    have h1 := hasDerivAt_id t
    have h2 := (h1.pow 2).const_mul X
    have h3 := ((h1.pow 3).const_mul (X ^ 2)).div_const 3
    convert (h1.add h2).add h3 using 1 <;>
      first
      | (funext y; simp [F, id, Pi.add_apply] <;> ring)
      | (simp [F, id] <;> ring)
  have hc : Continuous (fun t : ℝ => (1 + X * t) ^ 2) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable 0 h)]
  simp [F]
