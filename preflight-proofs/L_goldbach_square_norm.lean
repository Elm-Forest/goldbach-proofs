import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_square_norm :
    ∀ (S M : ℂ) (E : ℝ), ‖S-M‖≤E → ‖S^2-M^2‖≤E*(2*‖M‖+E) := by
  intro S M E herr
  have hE : 0 ≤ E := (norm_nonneg _).trans herr
  have hsum : ‖S + M‖ ≤ 2 * ‖M‖ + E := by
    calc
      ‖S + M‖ = ‖(S - M) + (M + M)‖ := by
        rw [show S + M = (S - M) + (M + M) by ring]
      _ ≤ ‖S - M‖ + ‖M + M‖ := norm_add_le _ _
      _ ≤ 2 * ‖M‖ + E := by
        have hM := norm_add_le M M
        linarith
  have hsq : ‖S ^ 2 - M ^ 2‖ ≤ E * (2 * ‖M‖ + E) := by
    rw [show S ^ 2 - M ^ 2 = (S - M) * (S + M) by ring, norm_mul]
    exact mul_le_mul herr hsum (norm_nonneg _) hE
  exact hsq
