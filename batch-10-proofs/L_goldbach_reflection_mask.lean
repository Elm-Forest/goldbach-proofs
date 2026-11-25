import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_reflection_mask :
    ∀ (n : ℕ) (a : ℕ → ℝ), (let b := fun k => if Nat.Prime k then a k else 0; (∑ k ∈ Finset.range (n+1), a k*a (n-k)) - (∑ k ∈ Finset.range (n+1), b k*b (n-k)) = ∑ k ∈ Finset.range (n+1), if Nat.Prime k ∧ Nat.Prime (n-k) then 0 else a k*a (n-k)) := by
  intro n a
  dsimp only
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h1 : Nat.Prime k <;> by_cases h2 : Nat.Prime (n-k) <;>
    simp [h1, h2]
