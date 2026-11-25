import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_reflect_isometry :
    ∀ (n : ℕ) (b : ℕ → ℂ), (∑ k ∈ Finset.range (n+1), ‖b (n-k)‖^2) = ∑ k ∈ Finset.range (n+1), ‖b k‖^2 := by
  intro n b
  refine Finset.sum_bij (fun k _ => n-k) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk l hl he
    simp only [Finset.mem_range] at hk hl
    omega
  · intro k hk
    have hh := Finset.mem_range.mp hk
    refine ⟨n-k, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk
    rfl
