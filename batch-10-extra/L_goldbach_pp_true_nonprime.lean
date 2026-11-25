import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_pp_true_nonprime :
    ∀ p a : ℕ, p.Prime → 2≤a → ¬ Nat.Prime (p^a) := by
  intro p a hp ha h
  have hd : p ∣ p^a := dvd_pow_self _ (by omega)
  rcases (Nat.dvd_prime h).mp hd with h1 | h1
  · exact hp.ne_one h1
  · have hp2 := hp.two_le
    have h2 : p^2 ≤ p^a := Nat.pow_le_pow_right (by omega) ha
    have h3 : p < p^2 := by
      simpa [pow_two] using Nat.mul_lt_mul_of_pos_left (show 1<p by omega) (show 0<p by omega)
    exact (ne_of_lt (h3.trans_le h2)) h1
