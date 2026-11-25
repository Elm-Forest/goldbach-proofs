import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_reflect_orthogonal :
    ∀ (n : ℕ) (b : ℕ → ℝ), (∑ k ∈ Finset.range (n+1), (b k + b (n-k))*(b k - b (n-k)))=0 := by
  intro n b
  have href : (∑ k ∈ Finset.range (n+1), (b (n-k))^2) =
      ∑ k ∈ Finset.range (n+1), (b k)^2 := by
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
  calc
    _ = ∑ k ∈ Finset.range (n+1), ((b k)^2-(b (n-k))^2) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 0 := by rw [Finset.sum_sub_distrib, href, sub_self]
