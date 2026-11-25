import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_rallis_gap_budget :
    ∀ A C B P M U V e f g : ℝ, 0 < A → |(P-M)-4*A*C| ≤ e → |P-U| ≤ f → |M-V| ≤ g → 4*A*B+e+f+g < U-V → B < C := by
  intro A C B P M U V e f g hA h1 h2 h3 h4
  have h5 := (abs_le.mp h1).2
  have h6 := (abs_le.mp h2).1
  have h7 := (abs_le.mp h3).2
  by_contra! hh
  have h8 := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 4*A)
  linarith
