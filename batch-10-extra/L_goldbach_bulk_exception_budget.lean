import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_bulk_exception_budget :
    ∀ (s : Finset ℕ) (r m : ℕ → ℝ) (L : ℝ), 0<L → (∀ n ∈ s, L ≤ m n) → (((s.filter (fun n => r n=0)).card : ℝ)*L^2) ≤ ∑ n ∈ s, (r n-m n)^2 := by
  intro s r m L hL hm
  calc
    _ = ∑ n ∈ s.filter (fun n => r n=0), L^2 := by simp
    _ ≤ ∑ n ∈ s.filter (fun n => r n=0), (r n-m n)^2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hs := Finset.mem_filter.mp hn
      have hh := hm n hs.1
      rw [hs.2, zero_sub, neg_sq]
      nlinarith [sq_nonneg (m n-L)]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => sq_nonneg _)
