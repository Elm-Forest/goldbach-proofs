import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_signed_cutoff_projector :
    ∀ (m : ℕ) (μ c : Fin m → ℝ) (t : ℝ), (∑ j, μ j*(c j)^2) ≤ t*(∑ j, (c j)^2) + ∑ j ∈ Finset.univ.filter (fun j => t<μ j), (μ j-t)*(c j)^2 := by
  intro m μ c t
  rw [Finset.mul_sum, ← Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  by_cases h : t < μ j
  · simp [h]
    ring_nf
    rfl
  · simp [h]
    exact mul_le_mul_of_nonneg_right (le_of_not_gt h) (sq_nonneg _)
