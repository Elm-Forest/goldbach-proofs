import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pp_base_unique :
    ∀ p q a b : ℕ, p.Prime → q.Prime → 0<a → 0<b → p^a=q^b → p=q := by
  intro p q a b hp hq ha hb h
  have hd : p ∣ q^b := by
    rw [← h]
    exact dvd_pow_self _ (by omega)
  have hd' : p ∣ q := hp.dvd_of_dvd_pow hd
  rcases (Nat.dvd_prime hq).mp hd' with h1 | h1
  · exact (hp.ne_one h1).elim
  · exact h1
