import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_zero_index_cross :
    ∀ (m : ℕ) (u : Fin m → ℂ), (∑ j, u j) * (∑ j, star (u j)) - (∑ j, u j * star (u j)) = ∑ j, ∑ l ∈ Finset.univ.erase j, u j * star (u l) := by
  intro m u
  rw [Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
    (fun l => u j * star (u l)) hj
  rw [Finset.mul_sum, ← h]
  ring
