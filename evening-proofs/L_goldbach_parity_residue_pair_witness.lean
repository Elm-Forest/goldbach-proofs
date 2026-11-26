import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_parity_residue_pair_witness :
    let liouville := fun n : ℕ => (-1:ℤ)^n.primeFactorsList.length; Nat.Prime 97 ∧ Nat.Prime 103 ∧ Nat.Prime 67 ∧ Nat.Prime 7 ∧ Nat.Prime 19 ∧ 133 = 7*19 ∧ 97+103=200 ∧ 67+133=200 ∧ (∀ x ∈ ({97,103,67,133} : Finset ℕ), 200 ≤ 3*x ∧ 3*x ≤ 400) ∧ (∀ m : ℕ, m ∣ 30 → ∀ F : ℕ → ℕ → ℝ, F (97 % m) (103 % m)=F (67 % m) (133 % m)) ∧ liouville 97 * liouville 103 = 1 ∧ liouville 67 * liouville 133 = -1 := by
  dsimp only
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> norm_num
  · intro m hm F
    have h1 : 97 % m = 67 % m := by
      rw [show (97:ℕ) = 67+30 by decide, Nat.add_mod, Nat.mod_eq_zero_of_dvd hm, add_zero, Nat.mod_mod]
    have h2 : 133 % m = 103 % m := by
      rw [show (133:ℕ) = 103+30 by decide, Nat.add_mod, Nat.mod_eq_zero_of_dvd hm, add_zero, Nat.mod_mod]
    rw [h1,h2]

  · rw [Nat.primeFactorsList_prime (by decide : Nat.Prime 97),
        Nat.primeFactorsList_prime (by decide : Nat.Prime 103)]
    norm_num
  · have h := (Nat.perm_primeFactorsList_mul (a := 7) (b := 19) (by decide) (by decide)).length_eq
    rw [show 7*19 = (133:ℕ) by decide,
        Nat.primeFactorsList_prime (by decide : Nat.Prime 7),
        Nat.primeFactorsList_prime (by decide : Nat.Prime 19)] at h
    rw [Nat.primeFactorsList_prime (by decide : Nat.Prime 67), h]
    norm_num
