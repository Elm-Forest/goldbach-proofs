import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_summed_width :
    ∀ (Q : ℕ) (h : ℕ → ℝ), (∀ q,0≤h q) → (∑ q ∈ Finset.Icc 1 Q, (Nat.totient q:ℝ)*(2*h q)) ≤ 2*∑ q ∈ Finset.Icc 1 Q,(q:ℝ)*h q := by
  intro Q h hh
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have ht : (Nat.totient q : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.totient_le q
  have hm := mul_le_mul_of_nonneg_right ht (hh q)
  linarith
