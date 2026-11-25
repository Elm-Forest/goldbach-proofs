import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pp_l1_budget :
    ∀ (n : ℕ) (s : Finset ℕ) (b : ℕ → ℝ) (L : ℝ), 0<n → (∀ k ∈ s, b k≤L^2) → (∑ k ∈ s, b k)/(n : ℝ) ≤ (s.card : ℝ)*L^2/n := by
  intro n s b L hn hb
  have h : (∑ k ∈ s, b k) ≤ (s.card : ℝ)*L^2 := by
    calc
      _ ≤ ∑ k ∈ s, L^2 := Finset.sum_le_sum hb
      _ = _ := by simp
  exact div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
