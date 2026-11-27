import Mathlib

/-!
Small independently replayable arithmetic interface extracted from
ShortProgressionsMeanTheta (XBribo, PR #3789,
a546c6629fae0223b56067d5e4ebc34043c4fbf1, Apache-2.0).
Names relocated to avoid duplicate OAI.Ostmann declarations when used
with DyadicCellShortPrimeFloor. Only elementary definitions and lemmas
are copied; none of the analytic black-box conclusions are assumed.
-/
open Finset Filter
open scoped Topology Classical
noncomputable section
namespace InnerFloorLinearTotient
set_option maxHeartbeats 1000000 in


private def squareMass : ℝ := ∑' n : ℕ, ((n:ℝ)^2)⁻¹
set_option maxHeartbeats 1000000 in

private theorem squareMass_nonneg : 0 ≤ squareMass := tsum_nonneg fun _ => by positivity
set_option maxHeartbeats 1000000 in

private theorem sum_square_inv_le (s : Finset ℕ) :
    (∑ n ∈ s, ((n:ℝ)^2)⁻¹) ≤ squareMass :=
  (Real.summable_nat_pow_inv.mpr (by decide : 1 < (2:ℕ))).sum_le_tsum s fun _ _ => by positivity
set_option maxHeartbeats 1000000 in

private theorem one_le_squareMass : 1 ≤ squareMass := by
  simpa using sum_square_inv_le {(1:ℕ)}

set_option maxHeartbeats 1000000 in
/-- Uniform constant for the reciprocal-totient mean and conductor lifting. -/
def weightConstant : ℝ := Real.exp (2*squareMass) * squareMass
set_option maxHeartbeats 1000000 in

theorem weightConstant_nonneg : 0 ≤ weightConstant :=
  mul_nonneg (Real.exp_pos _).le squareMass_nonneg
set_option maxHeartbeats 1000000 in

private theorem prime_factor_bound {p : ℕ} (hp : 2 ≤ p) :
    (1-(p:ℝ)⁻¹)⁻¹ ≤ (1+(p:ℝ)⁻¹)*(1+2*((p:ℝ)^2)⁻¹) := by
  let u := (p:ℝ)⁻¹
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu' : u ≤ 1/2 := by
    change (p:ℝ)⁻¹ ≤ 1/2
    rw [← one_div]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hp'
  have hden : 0 < 1-u := by linarith
  have hsq : u^2 ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ hu hu' 2
  have hnon := mul_nonneg (sq_nonneg u) (show 0 ≤ 1-2*u^2 by linarith)
  rw [← inv_pow]
  change (1-u)⁻¹ ≤ (1+u)*(1+2*u^2)
  rw [← one_div, div_le_iff₀ hden]
  nlinarith only [hnon]
set_option maxHeartbeats 1000000 in

private theorem squarefree_product_eq (q : ℕ) (hq : 0 < q) :
    (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) = ∑ d ∈ q.divisors with Squarefree d, (d:ℝ)⁻¹ := by
  rw [Finset.prod_one_add, Nat.sum_divisors_filter_squarefree hq.ne', Nat.factors_eq]
  refine sum_congr rfl fun s _ => ?_
  rw [Finset.prod_inv_distrib, ← Nat.cast_prod]
  rw [Finset.prod_eq_multiset_prod, show (fun i : ℕ => i) = id from rfl, Multiset.map_id]
set_option maxHeartbeats 1000000 in

private theorem ratio_le_divisors (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ Real.exp (2*squareMass) * ∑ d ∈ q.divisors, (d:ℝ)⁻¹ := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hEuler : (q.totient:ℝ) = (q:ℝ)*∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹) := by
    simpa only [map_natCast, map_mul, map_prod, map_sub, map_one, map_inv₀] using
      congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors q)
  have hlocal (p : ℕ) (hp : p ∈ q.primeFactors) : 0 ≤ (1-(p:ℝ)⁻¹)⁻¹ := by
    have hp' : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    apply inv_nonneg.mpr
    apply sub_nonneg.mpr
    exact inv_le_one_of_one_le₀ (by linarith)
  have hsq : (∏ p ∈ q.primeFactors, (1+2*((p:ℝ)^2)⁻¹)) ≤ Real.exp (2*squareMass) := by
    apply (Real.prod_one_add_le_exp_sum _ (fun _ => by positivity)).trans
    apply Real.exp_le_exp.mpr
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_square_inv_le _) (by norm_num)
  calc
    _ = ∏ p ∈ q.primeFactors, (1-(p:ℝ)⁻¹)⁻¹ := by
      rw [hEuler, div_mul_eq_div_div, div_self hq'.ne', one_div, Finset.prod_inv_distrib]
    _ ≤ ∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)*(1+2*((p:ℝ)^2)⁻¹) :=
      prod_le_prod₀ hlocal fun p hp => prime_factor_bound (Nat.prime_of_mem_primeFactors hp).two_le
    _ = (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) * (∏ p ∈ q.primeFactors, (1+2*((p:ℝ)^2)⁻¹)) :=
      Finset.prod_mul_distrib
    _ ≤ (∏ p ∈ q.primeFactors, (1+(p:ℝ)⁻¹)) * Real.exp (2*squareMass) :=
      mul_le_mul_of_nonneg_left hsq (prod_nonneg fun _ _ => by positivity)
    _ ≤ _ := by
      rw [mul_comm, squarefree_product_eq q hq]
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)) (Real.exp_pos _).le
set_option maxHeartbeats 1000000 in

private theorem harmonic_bound (Q : ℕ) :
    (∑ i ∈ Icc 1 Q, (i:ℝ)⁻¹) ≤ 1+Real.log Q := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    using harmonic_le_one_add_log Q

set_option maxHeartbeats 1000000 in
/-- Pointwise `q/φ(q)` also costs at most one logarithm. -/
theorem ratio_totient_le (q : ℕ) (hq : 0 < q) :
    (q:ℝ)/(q.totient:ℝ) ≤ weightConstant * (1+Real.log q) := by
  have hsub : q.divisors ⊆ Icc 1 q := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hq (Nat.dvd_of_mem_divisors hd)⟩
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q from hq))
  calc
    _ ≤ Real.exp (2*squareMass) * (1+Real.log q) :=
      (ratio_le_divisors q hq).trans (mul_le_mul_of_nonneg_left
        ((sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans (harmonic_bound q))
        (Real.exp_pos _).le)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_right (Real.exp_pos _).le one_le_squareMass) (by positivity)
set_option maxHeartbeats 1000000 in

private theorem sum_antidiagonal_le_product (Q : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ q ∈ Icc 1 Q, ∑ ab ∈ q.divisorsAntidiagonal, f ab.1*g ab.2) ≤
      (∑ a ∈ Icc 1 Q, f a)*(∑ b ∈ Icc 1 Q, g b) := by
  let S := Icc 1 Q
  let w (p : ℕ × ℕ) := f p.1*g p.2
  have hw (p : ℕ × ℕ) : 0 ≤ w p := mul_nonneg (hf _) (hg _)
  have hsub (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal ⊆ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    intro ab hab
    have hm (d : ℕ) (hd : d ∈ q.divisors) : d ∈ S :=
      mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        (Nat.le_of_dvd (mem_Icc.mp hq).1 (Nat.dvd_of_mem_divisors hd)).trans (mem_Icc.mp hq).2⟩
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ (Nat.fst_mem_divisors_of_mem_antidiagonal hab),
      hm _ (Nat.snd_mem_divisors_of_mem_antidiagonal hab)⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
  change (∑ q ∈ S, ∑ ab ∈ q.divisorsAntidiagonal, w ab) ≤ _
  calc
    _ ≤ ∑ q ∈ S, ∑ p ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), w p :=
      sum_le_sum fun q hq => sum_le_sum_of_subset_of_nonneg (hsub q hq) (fun p _ _ => hw p)
    _ = ∑ p ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), w p :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ p ∈ S ×ˢ S, w p := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => hw p)
    _ = (∑ a ∈ S, f a)*(∑ b ∈ S, g b) := by rw [sum_product, sum_mul_sum]
set_option maxHeartbeats 1000000 in

private theorem inv_totient_le_pairs (q : ℕ) (hq : 0 < q) :
    1/(q.totient:ℝ) ≤ Real.exp (2*squareMass) *
      ∑ ab ∈ q.divisorsAntidiagonal, ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹ := by
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  calc
    _ = ((q:ℝ)/(q.totient:ℝ))/q := by
      rw [div_right_comm, div_self hq'.ne']
    _ ≤ (Real.exp (2*squareMass) * ∑ d ∈ q.divisors, (d:ℝ)⁻¹)/q :=
      div_le_div_of_nonneg_right (ratio_le_divisors q hq) hq'.le
    _ = _ := by
      rw [mul_div_assoc, Finset.sum_div,
        ← Nat.sum_divisorsAntidiagonal (fun d _ => (d:ℝ)⁻¹/q) (n := q)]
      congr 1
      refine sum_congr rfl fun p hp => ?_
      rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul, div_eq_mul_inv,
        mul_inv, ← inv_pow, pow_two, mul_assoc]

set_option maxHeartbeats 1000000 in
/-- The sum of reciprocal totients costs one logarithm, uniformly in `Q`. -/
theorem sum_inv_totient_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, 1/(q.totient:ℝ)) ≤ weightConstant * (1+Real.log Q) := by
  calc
    _ ≤ Real.exp (2*squareMass) * (∑ q ∈ Icc 1 Q, ∑ ab ∈ q.divisorsAntidiagonal,
        ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹) := by
      rw [Finset.mul_sum]
      exact sum_le_sum fun q hq => inv_totient_le_pairs q (mem_Icc.mp hq).1
    _ ≤ Real.exp (2*squareMass) * ((∑ a ∈ Icc 1 Q, ((a:ℝ)^2)⁻¹)*(∑ b ∈ Icc 1 Q, (b:ℝ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (sum_antidiagonal_le_product Q (fun a => ((a:ℝ)^2)⁻¹) (fun b => (b:ℝ)⁻¹)
        (fun _ => by positivity) (fun _ => by positivity)) (Real.exp_pos _).le
    _ ≤ Real.exp (2*squareMass) * (squareMass*(1+Real.log Q)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (sum_square_inv_le _) (harmonic_bound Q)
        (sum_nonneg fun _ _ => by positivity) squareMass_nonneg) (Real.exp_pos _).le
    _ = _ := (mul_assoc ..).symm

set_option maxHeartbeats 1000000 in
/-- Conductor multiplicities lose a single logarithm, including `d = 1`. -/
theorem sum_conductor_weights (Q : ℕ) (F : ℕ → ℝ) (hF : ∀ d, 0 ≤ F d) :
    (∑ q ∈ Icc 1 Q, (∑ d ∈ q.divisors, F d)/(q.totient:ℝ)) ≤
      (∑ d ∈ Icc 1 Q, F d/(d.totient:ℝ)) * (weightConstant*(1+Real.log Q)) := by
  let f (d : ℕ) := F d/(d.totient:ℝ)
  let g (m : ℕ) := 1/(m.totient:ℝ)
  have hf (d : ℕ) : 0 ≤ f d := div_nonneg (hF d) (Nat.cast_nonneg _)
  have hg (m : ℕ) : 0 ≤ g m := by dsimp [g]; positivity
  have hterm (q : ℕ) : (∑ d ∈ q.divisors, F d)/(q.totient:ℝ) ≤
      ∑ p ∈ q.divisorsAntidiagonal, f p.1*g p.2 := by
    rw [Finset.sum_div, ← Nat.sum_divisorsAntidiagonal (fun d _ => F d/(q.totient:ℝ)) (n := q)]
    refine sum_le_sum fun p hp => ?_
    have h1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
    have h2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
    have h3 : 0 < (p.1.totient:ℝ)*(p.2.totient:ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.totient_pos.mpr h1) (Nat.totient_pos.mpr h2)
    have hφ := Nat.totient_super_multiplicative p.1 p.2
    rw [(Nat.mem_divisorsAntidiagonal.mp hp).1] at hφ
    calc
      _ ≤ F p.1/((p.1.totient:ℝ)*(p.2.totient:ℝ)) :=
        div_le_div_of_nonneg_left (hF _) h3 (by exact_mod_cast hφ)
      _ = _ := by
        simp only [f, g, div_eq_mul_inv, one_mul, mul_inv_rev]
        ring
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ∑ p ∈ q.divisorsAntidiagonal, f p.1*g p.2 := sum_le_sum fun q _ => hterm q
    _ ≤ (∑ d ∈ Icc 1 Q, f d)*(∑ m ∈ Icc 1 Q, g m) := sum_antidiagonal_le_product Q f g hf hg
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_totient_le Q) (sum_nonneg fun d _ => hf d)


/-- Uniform finite sum of reciprocal m*phi(m), with no logarithmic loss.
The antidiagonal inequality uses the divisor expansion already proved above. -/
theorem sum_inv_mul_totient_le (M : ℕ) :
    (∑ m ∈ Icc 1 M, (1:ℝ)/((m:ℝ)*(m.totient:ℝ))) ≤
      weightConstant * squareMass := by
  calc
    _ ≤ Real.exp (2*squareMass) *
        (∑ m ∈ Icc 1 M, ∑ ab ∈ m.divisorsAntidiagonal,
          ((ab.1:ℝ)^2)⁻¹ * ((ab.2:ℝ)^2)⁻¹) := by
      rw [Finset.mul_sum]
      apply sum_le_sum
      intro m hm
      have hm0 : 0 < (m:ℝ) := by exact_mod_cast (mem_Icc.mp hm).1
      calc
        _ = (1/(m.totient:ℝ))/(m:ℝ) := by ring
        _ ≤ (Real.exp (2*squareMass) *
              ∑ ab ∈ m.divisorsAntidiagonal,
                ((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹)/(m:ℝ) :=
          div_le_div_of_nonneg_right (inv_totient_le_pairs m (mem_Icc.mp hm).1) hm0.le
        _ = Real.exp (2*squareMass) *
              ∑ ab ∈ m.divisorsAntidiagonal,
                (((ab.1:ℝ)^2)⁻¹*(ab.2:ℝ)⁻¹)/(m:ℝ) := by
          rw [mul_div_assoc, Finset.sum_div]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          apply sum_le_sum
          intro p hp
          have ha : 1 ≤ p.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hp)
          have hb : 1 ≤ p.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hp)
          have haR : (1:ℝ) ≤ p.1 := by exact_mod_cast ha
          have hbR : (1:ℝ) ≤ p.2 := by exact_mod_cast hb
          have ha0 : (0:ℝ) < p.1 := by linarith
          have hb0 : (0:ℝ) < p.2 := by linarith
          rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, Nat.cast_mul]
          apply (div_le_iff₀ (mul_pos ha0 hb0)).2
          have h := mul_le_mul_of_nonneg_right haR (show 0 ≤ ((p.1:ℝ)^2)⁻¹ * (p.2:ℝ)⁻¹ by positivity)
          calc
            _ ≤ (p.1:ℝ) * (((p.1:ℝ)^2)⁻¹ * (p.2:ℝ)⁻¹) := by simpa using h
            _ = ((p.1:ℝ)^2)⁻¹ * ((p.2:ℝ)^2)⁻¹ * ((p.1:ℝ)*(p.2:ℝ)) := by
              field_simp <;> ring
    _ ≤ Real.exp (2*squareMass) *
        ((∑ a ∈ Icc 1 M, ((a:ℝ)^2)⁻¹) *
          (∑ b ∈ Icc 1 M, ((b:ℝ)^2)⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (sum_antidiagonal_le_product M (fun a => ((a:ℝ)^2)⁻¹)
          (fun b => ((b:ℝ)^2)⁻¹) (fun _ => by positivity) (fun _ => by positivity))
        (Real.exp_pos _).le
    _ ≤ Real.exp (2*squareMass) * (squareMass * squareMass) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (sum_square_inv_le _) (sum_square_inv_le _)
          (sum_nonneg fun _ _ => by positivity) squareMass_nonneg) (Real.exp_pos _).le
    _ = _ := by unfold weightConstant; ring

/-- Explicit uniform constant, independent of the conductor and the cutoff. -/
def exceptionalWeightConstant : ℝ := weightConstant * squareMass

theorem exceptionalWeightConstant_nonneg : 0 ≤ exceptionalWeightConstant :=
  mul_nonneg weightConstant_nonneg squareMass_nonneg

/-- Finite weighted bound for the isolated zero-model diagonal.
The hypotheses expose the two analytic/arithmetic inputs separately:
the coefficient is bounded by 1/phi(m), and the integral by C*U/(d*m).
No assertion about actual prime sums is made. -/
theorem isolatedPacket_bound (S : Finset ℕ) (M d : ℕ) (hd : 0 < d)
    (hS : S ⊆ Icc 1 M) (U C X : ℝ) (hU : 0 ≤ U)
    (hC : 0 ≤ C) (hX : 0 ≤ X) (a I : ℕ → ℝ)
    (ha : ∀ m ∈ S, |a m| ≤ 1/(m.totient:ℝ))
    (hI : ∀ m ∈ S, |I m| ≤ C*U/((d:ℝ)*(m:ℝ))) :
    |((d:ℝ)/(d.totient:ℝ))*X*(∑ m ∈ S, a m * I m)| ≤
      C*exceptionalWeightConstant*X*U/(d.totient:ℝ) := by
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hphi : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hnon : 0 ≤ (d:ℝ)/(d.totient:ℝ)*X := by positivity
  have hsum : (∑ m ∈ S, 1/((m:ℝ)*(m.totient:ℝ))) ≤ exceptionalWeightConstant :=
    (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (sum_inv_mul_totient_le M)
  rw [abs_mul, abs_of_nonneg hnon]
  calc
    _ ≤ ((d:ℝ)/(d.totient:ℝ))*X*(∑ m ∈ S, |a m * I m|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hnon
    _ ≤ ((d:ℝ)/(d.totient:ℝ))*X*
        (∑ m ∈ S, (C*U/(d:ℝ))*(1/((m:ℝ)*(m.totient:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ hnon
      apply sum_le_sum
      intro m hm
      rw [abs_mul]
      calc
        _ ≤ (1/(m.totient:ℝ))*(C*U/((d:ℝ)*(m:ℝ))) :=
          mul_le_mul (ha m hm) (hI m hm) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ ((d:ℝ)/(d.totient:ℝ))*X*(C*U/(d:ℝ)*exceptionalWeightConstant) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hnon
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp <;> ring

/-- The common-conductor packet estimate. For two primitive characters
of conductors d1 and d2, take L = lcm d1 d2 and g = sqrt(d1*d2).
The Gauss bound and the common-level totient inequality yield the
hypothesis on a. No sign or independence assumption is made. -/
theorem commonMultiplePacket_bound (S : Finset ℕ) (M L : ℕ) (hL : 0 < L)
    (hS : S ⊆ Icc 1 M) (g U C X : ℝ) (hg : 0 ≤ g) (hgL : g ≤ L)
    (hU : 0 ≤ U) (hC : 0 ≤ C) (hX : 0 ≤ X) (a I : ℕ → ℝ)
    (ha : ∀ m ∈ S, |a m| ≤ g/((L*m).totient:ℝ))
    (hI : ∀ m ∈ S, |I m| ≤ C*U/((L*m:ℕ):ℝ)) :
    |X*(∑ m ∈ S, a m * I m)| ≤
      C*exceptionalWeightConstant*X*U/(L.totient:ℝ) := by
  have hLR : 0 < (L:ℝ) := by exact_mod_cast hL
  have hphi : 0 < (L.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hL
  have hsum : (∑ m ∈ S, 1/((m:ℝ)*(m.totient:ℝ))) ≤ exceptionalWeightConstant :=
    (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (sum_inv_mul_totient_le M)
  have hterm (m : ℕ) (hm : m ∈ S) :
      |a m*I m| ≤ (C*U/(L.totient:ℝ))*(1/((m:ℝ)*(m.totient:ℝ))) := by
    have hm0 : 0 < m := (mem_Icc.mp (hS hm)).1
    have hmR : 0 < (m:ℝ) := by exact_mod_cast hm0
    have hmφ : 0 < (m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm0
    have hφ : (L.totient:ℝ)*(m.totient:ℝ) ≤ ((L*m).totient:ℝ) := by
      exact_mod_cast Nat.totient_super_multiplicative L m
    have hal := (ha m hm).trans (div_le_div_of_nonneg_left hg (mul_pos hphi hmφ) hφ)
    rw [abs_mul]
    calc
      _ ≤ (g/((L.totient:ℝ)*(m.totient:ℝ)))*(C*U/((L*m:ℕ):ℝ)) :=
        mul_le_mul hal (hI m hm) (abs_nonneg _) (by positivity)
      _ ≤ ((L:ℝ)/((L.totient:ℝ)*(m.totient:ℝ)))*(C*U/((L*m:ℕ):ℝ)) := by
        gcongr
      _ = _ := by rw [Nat.cast_mul]; field_simp <;> ring
  rw [abs_mul,abs_of_nonneg hX]
  calc
    _ ≤ X*(∑ m ∈ S, |a m*I m|) :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hX
    _ ≤ X*(∑ m ∈ S, (C*U/(L.totient:ℝ))*(1/((m:ℝ)*(m.totient:ℝ)))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hterm) hX
    _ ≤ X*(C*U/(L.totient:ℝ)*exceptionalWeightConstant) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsum (by positivity)) hX
    _ = _ := by ring

/-- The conductor weight is uniformly little-o after any fixed polylog loss.
This handles arbitrary finite pairs whose lcm is at least n^(1/6+delta). -/
theorem eventualLargeConductorWeight (δ k ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      (n:ℝ)^(1/6+δ) ≤ d → d ≤ n →
      (Real.log (n:ℝ))^k*(n:ℝ)^(1/6:ℝ)/(d.totient:ℝ) ≤ ε := by
  have hnlim : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  let W := weightConstant
  have hW : 0 ≤ W := weightConstant_nonneg
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (k+1) hδ).comp_tendsto hnlim).bound
    (show 0 < ε/(2*W+1) by positivity)
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (Real.tendsto_log_atTop.comp hnlim).eventually_ge_atTop 1,hsmall]
    with n hn hlog hsmall
  intro d hd hdn
  let L := Real.log (n:ℝ)
  let v := (n:ℝ)^(1/6:ℝ)
  let w := (n:ℝ)^δ
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL1 : 1 ≤ L := hlog
  have hL0 : 0 < L := by linarith
  have hv : 0 < v := Real.rpow_pos_of_pos hn0 _
  have hw : 0 < w := Real.rpow_pos_of_pos hn0 _
  have hpow : v*w = (n:ℝ)^(1/6+δ) := by
    dsimp [v,w]
    rw [← Real.rpow_add hn0]
  have hvd : v*w ≤ (d:ℝ) := by rw [hpow]; exact hd
  have hdR : 0 < (d:ℝ) := (mul_pos hv hw).trans_le hvd
  have hdN : 0 < d := by exact_mod_cast hdR
  have hφ : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hdN
  have hdnR : (d:ℝ) ≤ n := by exact_mod_cast hdn
  have hlogd : Real.log (d:ℝ) ≤ L := Real.log_le_log hdR hdnR
  have hratio : (d:ℝ)/(d.totient:ℝ) ≤ 2*W*L := by
    calc
      _ ≤ W*(1+Real.log d) := ratio_totient_le d hdN
      _ ≤ W*(2*L) := mul_le_mul_of_nonneg_left (by linarith) hW
      _ = _ := by ring
  have hvw : v/(d:ℝ) ≤ 1/w := by
    rw [div_le_div_iff₀ hdR hw]
    simpa using hvd
  have hsl : L^(k+1) ≤ ε/(2*W+1)*w := by
    change ‖Real.log (n:ℝ)^(k+1)‖ ≤ ε/(2*W+1)*‖(n:ℝ)^δ‖ at hsmall
    simpa only [L,w,Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)] using hsmall
  have hpowL : L^k*L = L^(k+1) := by
    rw [Real.rpow_add hL0,Real.rpow_one]
  change L^k*v/(d.totient:ℝ) ≤ ε
  calc
    _ = L^k*((d:ℝ)/(d.totient:ℝ))*(v/(d:ℝ)) := by field_simp <;> ring
    _ ≤ L^k*(2*W*L)*(1/w) := by gcongr
    _ = 2*W*(L^(k+1)/w) := by rw [← hpowL]; ring
    _ ≤ 2*W*(ε/(2*W+1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_iff₀ hw).2 hsl
    _ ≤ ε := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 2*W+1)).2
      linarith

end InnerFloorLinearTotient

end



/-! Uniform, sign-independent estimates for the exact continuous zero
models on the scaled inner arcs. No zero-free hypothesis or assertion
about actual primes is used in these lemmas. -/
open MeasureTheory
open scoped Interval
namespace InnerFloorZeroModel
noncomputable section

def phase (s : ℝ) : ℂ := Complex.exp ((s:ℂ)*Complex.I)

@[simp] theorem norm_phase (s : ℝ) : ‖phase s‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I s

def transform (β γ v : ℝ) : ℂ :=
  ∫ x in (0:ℝ)..1, (x^(β-1):ℝ) • phase (γ*Real.log x + 2*Real.pi*v*x)

theorem transform_norm_le (β γ v : ℝ) (hβ : 0 < β) :
    ‖transform β γ v‖ ≤ 1/β := by
  unfold transform
  apply (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans_eq
  have he : (∫ x in (0:ℝ)..1,
        ‖(x^(β-1):ℝ) • phase (γ*Real.log x + 2*Real.pi*v*x)‖) =
      ∫ x in (0:ℝ)..1, x^(β-1) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    change ‖(x^(β-1):ℝ) • phase (γ*Real.log x + 2*Real.pi*v*x)‖ = x^(β-1)
    rw [norm_smul, norm_phase, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hx.1 _)]
  rw [he, integral_rpow (Or.inl (by linarith : -1 < β-1))]
  rw [show β-1+1=β by ring, Real.one_rpow, Real.zero_rpow hβ.ne', sub_zero]

def pairIntegral (β₁ γ₁ β₂ γ₂ L : ℝ) : ℂ :=
  ∫ v in (-L)..L, transform β₁ γ₁ v * transform β₂ γ₂ v *
    phase (-(2*Real.pi*v))

theorem pairIntegral_norm_le (β₁ γ₁ β₂ γ₂ L : ℝ)
    (h₁ : 0 < β₁) (h₂ : 0 < β₂) (hL : 0≤L) :
    ‖pairIntegral β₁ γ₁ β₂ γ₂ L‖ ≤ (2*L)/(β₁*β₂) := by
  unfold pairIntegral
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -L) (b := L) (C := (1/β₁)*(1/β₂))
    (f := fun v => transform β₁ γ₁ v * transform β₂ γ₂ v * phase (-(2*Real.pi*v)))
    (fun v _ => by
      rw [norm_mul, norm_mul, norm_phase, mul_one]
      exact mul_le_mul (transform_norm_le β₁ γ₁ v h₁)
        (transform_norm_le β₂ γ₂ v h₂) (norm_nonneg _) (by positivity))
  calc
    _ ≤ |L-(-L)| * ((1/β₁)*(1/β₂)) := by simpa [mul_comm] using h
    _ = _ := by rw [abs_of_nonneg (by linarith)]; ring

/-- Uniform bound for near-one pairs (valid throughout beta >= 1/2). -/
theorem pairIntegral_nearOne (β₁ γ₁ β₂ γ₂ L : ℝ)
    (h₁ : 1/2≤β₁) (h₂ : 1/2≤β₂) (hL : 0≤L) :
    ‖pairIntegral β₁ γ₁ β₂ γ₂ L‖ ≤ 8*L := by
  apply (pairIntegral_norm_le β₁ γ₁ β₂ γ₂ L (by linarith) (by linarith) hL).trans
  have hb : 1/4 ≤ β₁*β₂ := by
    have := mul_le_mul h₁ h₂ (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤β₁)
    linarith
  calc
    _ ≤ (2*L)/(1/4:ℝ) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hb
    _ = _ := by ring

end
end InnerFloorZeroModel

open Finset Filter InnerFloorLinearTotient
open scoped Classical Topology
namespace InnerFloorZeroModel
noncomputable section
set_option maxHeartbeats 2000000

/-- Actual continuous pair-integrals fit the verified conductor-packet
bound for all gamma, not just for real zeros. The arithmetic coefficient
bound must still be supplied by the actual Gauss-character expansion. -/
theorem continuousPacket_bound (S : Finset ℕ) (M L : ℕ) (hL : 0 < L)
    (hS : S ⊆ Icc 1 M) (g U X β₁ γ₁ β₂ γ₂ : ℝ)
    (hg : 0≤g) (hgL : g≤L) (hU : 0≤U) (hX : 0≤X)
    (hβ₁ : 1/2≤β₁) (hβ₂ : 1/2≤β₂)
    (a : ℕ → ℂ)
    (ha : ∀ m∈S, ‖a m‖≤g/((L*m).totient:ℝ)) :
    ‖(X:ℂ)*(∑ m∈S, a m * pairIntegral β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ)))‖ ≤
      8*exceptionalWeightConstant*X*U/(L.totient:ℝ) := by
  let I (m : ℕ) := pairIntegral β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ))
  have hI : ∀ m∈S, |‖I m‖|≤8*U/((L*m:ℕ):ℝ) := by
    intro m hm
    rw [abs_of_nonneg (norm_nonneg _)]
    have h := pairIntegral_nearOne β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ))
      hβ₁ hβ₂ (by positivity)
    dsimp [I]
    exact h.trans_eq (by ring)
  have hW := commonMultiplePacket_bound S M L hL hS g U 8 X hg hgL hU
    (by norm_num) hX (fun m => ‖a m‖) (fun m => ‖I m‖)
    (fun m hm => by simpa only [abs_of_nonneg (norm_nonneg _)] using ha m hm) hI
  have hsum0 : 0≤X*(∑ m∈S, ‖a m‖*‖I m‖) :=
    mul_nonneg hX (sum_nonneg fun m _ => by positivity)
  rw [abs_of_nonneg hsum0] at hW
  change ‖(X:ℂ)*(∑ m∈S, a m*I m)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX]
  apply le_trans _ hW
  apply mul_le_mul_of_nonneg_left _ hX
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])

/-- A finite family of large-common-conductor model pairs with any fixed
polylogarithmic cardinality and beta <= 1 is negligible in total.
The input U <= C * log(n)^2 * n^(1/6) is the frozen inner width. -/
theorem sparseLargePackets_o (δ k C ε : ℝ) (hδ : 0 < δ) (hC : 0≤C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (T : Finset ℕ) (D : ℕ → ℕ) (J : ℕ → ℂ),
        (T.card:ℝ) ≤ (Real.log (n:ℝ))^k →
        (∀ i∈T, (n:ℝ)^(1/6+δ)≤D i ∧ D i≤n) →
        (∀ i∈T, ‖J i‖ ≤ C*(n:ℝ)*(Real.log (n:ℝ))^2*
          (n:ℝ)^(1/6:ℝ)/( (D i).totient:ℝ)) →
        ‖∑ i∈T, J i‖ ≤ ε*(n:ℝ) := by
  have hlim : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (Real.tendsto_log_atTop.comp hlim).eventually_ge_atTop 1,
    eventualLargeConductorWeight δ (k+2) (ε/(C+1)) hδ (by positivity)]
    with n hn hlog hweight
  intro T D J hcard hD hJ
  let L := Real.log (n:ℝ)
  let v := (n:ℝ)^(1/6:ℝ)
  have hL1 : 1≤L := hlog
  have hL : 0 < L := by linarith
  have hpow : 0 < L^k := Real.rpow_pos_of_pos hL _
  have hLadd : L^(k+2) = L^k*L^2 := by rw [Real.rpow_add hL, Real.rpow_two]
  have hterm (i : ℕ) (hi : i∈T) :
      ‖J i‖ ≤ ε*(n:ℝ)/L^k := by
    obtain ⟨h₁,h₂⟩ := hD i hi
    have hw := hweight (D i) h₁ h₂
    change L^(k+2)*v/((D i).totient:ℝ) ≤ ε/(C+1) at hw
    rw [hLadd] at hw
    apply (le_div_iff₀ hpow).2
    calc
      ‖J i‖*L^k ≤ (C*(n:ℝ)*L^2*v/((D i).totient:ℝ))*L^k :=
        mul_le_mul_of_nonneg_right (hJ i hi) hpow.le
      _ = C*(n:ℝ)*(L^k*L^2*v/((D i).totient:ℝ)) := by ring
      _ ≤ C*(n:ℝ)*(ε/(C+1)) := mul_le_mul_of_nonneg_left hw (by positivity)
      _ ≤ ε*(n:ℝ) := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : 0 < C+1)).2
        nlinarith only [mul_nonneg hε.le (Nat.cast_nonneg n : (0:ℝ)≤n)]
  calc
    _ ≤ ∑ i∈T, ‖J i‖ := norm_sum_le _ _
    _ ≤ ∑ i∈T, ε*(n:ℝ)/L^k := sum_le_sum hterm
    _ = (T.card:ℝ)*(ε*(n:ℝ)/L^k) := by simp
    _ ≤ L^k*(ε*(n:ℝ)/L^k) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp

end
end InnerFloorZeroModel
#print axioms InnerFloorZeroModel.continuousPacket_bound
#print axioms InnerFloorZeroModel.sparseLargePackets_o

/-!
The Gauss lifting lemmas below are extracted from the community's accepted
PEqualNP.Outside.L_goldbach_frontier_type2_b1_b4, as stored in
alternate-signed/Type2B1B4Accepted.lean from the official main checkout.
Original proofs are retained; only the small necessary namespaces are used.
Apache-2.0 upstream license. This is a research-only standalone replay.
-/
open Finset
namespace BombieriVinogradov.LargeSieve
open Complex Real
noncomputable section
def additivePhase (x : ℝ) : ℂ := circleMap 0 1 (2 * Real.pi * x)

theorem additivePhase_add (x y : ℝ) : additivePhase (x + y) = additivePhase x * additivePhase y := by
  dsimp [additivePhase]
  rw [circleMap_zero_mul, one_mul, mul_add]


end
end BombieriVinogradov.LargeSieve
namespace DyadicMixedB4DualCharacter
theorem sum_natCast_range_eq_zmod {R : Type*} [AddCommMonoid R] {q : ℕ} [NeZero q] (f : ZMod q → R) :
    ∑ u ∈ range q, f (u : ZMod q) = ∑ z : ZMod q, f z := by
  apply sum_bij (s := range q) (t := (univ : Finset (ZMod q))) (fun u _ => (u : ZMod q))
  · simp
  · intro u uMember v vMember equal
    have valEqual := congrArg ZMod.val equal
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp uMember),
      Nat.mod_eq_of_lt (mem_range.mp vMember)] using valEqual
  · intro z _
    exact ⟨z.val, mem_range.mpr (ZMod.val_lt z), ZMod.natCast_zmod_val z⟩
  · intro u _
    rfl


end DyadicMixedB4DualCharacter

section

open Finset BombieriVinogradov.LargeSieve DyadicMixedB4DualCharacter
open scoped Classical

namespace DyadicMixedB4GaussLift

noncomputable section

theorem sum_range_blocks {R : Type*} [AddCommMonoid R] (d f : ℕ) (F : ℕ → R) :
    ∑ x ∈ range (d * f), F x = ∑ j ∈ range f, ∑ a ∈ range d, F (d * j + a) := by
  induction f with
  | zero => simp
  | succ f ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

theorem stdAddChar_nat_fraction {q : ℕ} [NeZero q] (k : ℕ) :
    ZMod.stdAddChar (k : ZMod q) = additivePhase ((k : ℝ) / q) := by
  rw [← Int.cast_natCast k, ZMod.stdAddChar_coe]
  unfold additivePhase
  rw [circleMap_zero, Complex.ofReal_one, one_mul]
  push_cast
  congr 1
  ring

theorem stdAddChar_mul_nat_fraction {q : ℕ} [NeZero q] (k a : ℕ) :
    ZMod.stdAddChar ((k : ZMod q) * (a : ZMod q)) = additivePhase ((k : ℝ) * a / q) := by
  rw [← Nat.cast_mul, stdAddChar_nat_fraction, Nat.cast_mul]

set_option maxHeartbeats 600000 in
theorem sum_phase_fraction_eq_if_dvd {q : ℕ} [NeZero q] (k : ℕ) :
    (∑ a ∈ range q, additivePhase ((k : ℝ) * a / q)) = if q ∣ k then (q : ℂ) else 0 := by
  simp_rw [← stdAddChar_mul_nat_fraction]
  rw [sum_natCast_range_eq_zmod (fun z => ZMod.stdAddChar ((k : ZMod q) * z))]
  simp_rw [mul_comm (k : ZMod q)]
  rw [AddChar.sum_mulShift (k : ZMod q) (ZMod.isPrimitive_stdAddChar q), ZMod.card]
  have zeroIff : (k : ZMod q) = 0 ↔ q ∣ k := by rw [ZMod.natCast_eq_zero_iff]
  by_cases divides : q ∣ k
  · simp [divides, zeroIff.mpr divides]
  · have nonzero : (k : ZMod q) ≠ 0 := fun zero => divides (zeroIff.mp zero)
    simp [divides, nonzero]

theorem gaussSum_as_fraction_sum {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum χ (ZMod.stdAddChar.mulShift (k : ZMod d)) =
      ∑ a ∈ range d, χ (a : ZMod d) * additivePhase ((k : ℝ) * a / d) := by
  unfold gaussSum
  rw [← sum_natCast_range_eq_zmod]
  simp_rw [AddChar.mulShift_apply, stdAddChar_mul_nat_fraction]

set_option maxHeartbeats 600000 in
theorem lift_gaussSum {d f : ℕ} [NeZero d] [NeZero f]
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    (∑ u ∈ range (d * f), χ (u : ZMod d) * additivePhase ((k : ℝ) * u / ((d : ℝ) * f))) =
      if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
  have dNonzero : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have fNonzero : (f : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne f
  rw [sum_range_blocks, Finset.sum_comm]
  have liftEntry (a j : ℕ) :
      χ ((d * j + a : ℕ) : ZMod d) * additivePhase ((k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f)) =
        (χ (a : ZMod d) * additivePhase ((k : ℝ) * a / ((d : ℝ) * f))) *
          additivePhase ((k : ℝ) * j / f) := by
    have angle : (k : ℝ) * (d * j + a : ℕ) / ((d : ℝ) * f) =
        (k : ℝ) * a / ((d : ℝ) * f) + (k : ℝ) * j / f := by
      push_cast
      field_simp
      ring
    rw [angle, additivePhase_add, ← mul_assoc]
    have same : ((d * j + a : ℕ) : ZMod d) = (a : ZMod d) := by push_cast; simp
    rw [same]
  simp_rw [liftEntry, ← mul_sum, sum_phase_fraction_eq_if_dvd]
  by_cases divisible : f ∣ k
  · simp only [if_pos divisible, ← Finset.sum_mul, gaussSum_as_fraction_sum]
    rw [mul_comm _ (f : ℂ)]
    apply congrArg (fun z : ℂ => (f : ℂ) * z)
    refine sum_congr rfl fun a _ => ?_
    have h : (k : ℝ) = ((k / f : ℕ) : ℝ) * f := by
      exact_mod_cast (Nat.div_mul_cancel divisible).symm
    have sameAngle : (k : ℝ) * a / ((d : ℝ) * f) = (((k / f : ℕ) : ℝ)) * a / d := by
      conv_lhs => rw [h]
      field_simp
    rw [sameAngle]
  · simp [divisible]


end
end DyadicMixedB4GaussLift

end

section

open Finset ArithmeticFunction BombieriVinogradov.LargeSieve DyadicMixedB4GaussLift
open scoped ArithmeticFunction.Moebius Classical

namespace DyadicMixedB4MoebiusGauss

noncomputable section

def moebiusComplex (m : ℕ) : ℂ := (μ m : ℂ)

theorem norm_moebiusComplex_le_one (m : ℕ) : ‖moebiusComplex m‖ ≤ 1 := by
  rw [moebiusComplex, Complex.norm_intCast]
  exact_mod_cast (abs_moebius_le_one (n := m))

theorem moebius_coprime_indicator {M : ℕ} (MPositive : 0 < M) (u : ℕ) :
    (∑ e ∈ M.divisors.filter (fun e => e ∣ u), moebiusComplex e) =
      if u.Coprime M then (1 : ℂ) else 0 := by
  let g := u.gcd M
  have gPositive : 0 < g := Nat.gcd_pos_of_pos_right u MPositive
  have divisorsEquality : M.divisors.filter (fun e => e ∣ u) = g.divisors := by
    ext e
    rw [mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨eDividesM, _⟩, eDividesU⟩
      exact ⟨Nat.dvd_gcd eDividesU eDividesM, gPositive.ne'⟩
    · rintro ⟨eDividesG, _⟩
      exact ⟨⟨eDividesG.trans (Nat.gcd_dvd_right u M), MPositive.ne'⟩,
        eDividesG.trans (Nat.gcd_dvd_left u M)⟩
  have convolution : (∑ e ∈ g.divisors, μ e) = (1 : ArithmeticFunction ℤ) g := by
    rw [← coe_mul_zeta_apply (f := μ), moebius_mul_coe_zeta]
  rw [divisorsEquality]
  simp_rw [moebiusComplex, ← Int.cast_sum, convolution]
  change (((1 : ArithmeticFunction ℤ) g : ℤ) : ℂ) = if g = 1 then (1 : ℂ) else 0
  by_cases one : g = 1
  · simp [one, one_apply]
  · simp [one, one_apply]

theorem changeLevel_nat_indicator {d M : ℕ} (dDivides : d ∣ M) (χ : DirichletCharacter ℂ d)
    (u : ℕ) : DirichletCharacter.changeLevel dDivides χ (u : ZMod M) =
      (if u.Coprime M then (1 : ℂ) else 0) * χ (u : ZMod d) := by
  by_cases coprime : u.Coprime M
  · rw [if_pos coprime, one_mul]
    have same := DirichletCharacter.changeLevel_eq_cast_of_dvd χ dDivides (ZMod.unitOfCoprime u coprime)
    rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast dDivides] at same
    exact same
  · rw [if_neg coprime, zero_mul]
    exact MulChar.map_nonunit _ (fun unit => coprime ((ZMod.isUnit_iff_coprime u M).mp unit))

theorem sum_filter_dvd_range {R : Type*} [AddCommMonoid R] {e M : ℕ}
    (ePositive : 0 < e) (eDivides : e ∣ M) (F : ℕ → R) :
    (∑ u ∈ (range M).filter (fun u => e ∣ u), F u) = ∑ v ∈ range (M / e), F (e * v) := by
  have quotient : e * (M / e) = M := Nat.mul_div_cancel' eDivides
  symm
  apply sum_bij (s := range (M / e)) (t := (range M).filter (fun u => e ∣ u)) (fun v _ => e * v)
  · intro v vMember
    refine mem_filter.mpr ⟨mem_range.mpr ?_, dvd_mul_right e v⟩
    rw [← quotient]
    exact Nat.mul_lt_mul_of_pos_left (mem_range.mp vMember) ePositive
  · intro v _ w _ eq
    exact Nat.eq_of_mul_eq_mul_left ePositive eq
  · intro u uMember
    obtain ⟨uRange, v, h⟩ := mem_filter.mp uMember
    refine ⟨v, mem_range.mpr ?_, h.symm⟩
    have prodLt : e * v < e * (M / e) := h ▸ quotient.symm ▸ mem_range.mp uRange
    exact Nat.lt_of_mul_lt_mul_left prodLt
  · intro v _
    rfl

theorem sum_inducedGauss_moebius {d M : ℕ} [NeZero M] (dDivides : d ∣ M)
    (χ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M)) =
      ∑ e ∈ M.divisors, moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) * additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) := by
  rw [gaussSum_as_fraction_sum]
  calc
    _ = ∑ u ∈ range M, ∑ e ∈ M.divisors.filter (fun e => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      refine sum_congr rfl fun u _ => ?_
      rw [changeLevel_nat_indicator, ← moebius_coprime_indicator (NeZero.pos M), mul_assoc, sum_mul]
    _ = ∑ e ∈ M.divisors, ∑ u ∈ (range M).filter (fun u => e ∣ u),
        moebiusComplex e * (χ (u : ZMod d) * additivePhase ((k : ℝ) * u / M)) := by
      simp_rw [sum_filter]
      exact sum_comm
    _ = _ := by
      refine sum_congr rfl fun e eMember => ?_
      have eDivides := (Nat.mem_divisors.mp eMember).1
      have ePositive := Nat.pos_of_mem_divisors eMember
      have eNonzero : (e : ℝ) ≠ 0 := by exact_mod_cast ePositive.ne'
      have MNonzero : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
      have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
      have quotientNonzero : ((M / e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast quotientPositive.ne'
      have quotient : (M : ℝ) = e * ((M / e : ℕ) : ℝ) := by
        exact_mod_cast (Nat.mul_div_cancel' eDivides).symm
      rw [sum_filter_dvd_range ePositive eDivides, mul_sum]
      refine sum_congr rfl fun v _ => ?_
      have scales : (k : ℝ) * (e * v : ℕ) / M = (k : ℝ) * v / ((M / e : ℕ) : ℝ) := by
        push_cast
        rw [quotient]
        field_simp
      rw [scales, Nat.cast_mul, map_mul]
      ring


end
end DyadicMixedB4MoebiusGauss

end

section

open Finset DyadicMixedB4GaussLift DyadicMixedB4MoebiusGauss
open scoped Classical

namespace DyadicMixedB4ImprimitiveBound

noncomputable section

theorem norm_primitive_gauss_shift_le {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (primitive : χ.IsPrimitive) (x : ZMod d) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ ≤ Real.sqrt d := by
  rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar primitive, norm_mul,
    DirichletCharacter.norm_gaussSum_stdAddChar primitive]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (DirichletCharacter.norm_le_one _ _)

theorem conductor_cofactor {M d e : ℕ} [NeZero d] [NeZero M] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (coprime : e.Coprime d) :
    0 < M / e / d ∧ d * (M / e / d) = M / e ∧ e * (d * (M / e / d)) = M := by
  have eDivides := (Nat.mem_divisors.mp eMember).1
  have ePositive := Nat.pos_of_mem_divisors eMember
  have quotientPositive : 0 < M / e := Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) eDivides) ePositive
  have joint : e * d ∣ M := coprime.mul_dvd_of_dvd_of_dvd eDivides dDivides
  have dividesQuotient : d ∣ M / e := (Nat.dvd_div_iff_mul_dvd eDivides).mpr (by simpa [mul_comm] using joint)
  have quotient := Nat.mul_div_cancel' dividesQuotient
  exact ⟨Nat.div_pos (Nat.le_of_dvd quotientPositive dividesQuotient) (NeZero.pos d), quotient,
    by rw [quotient, Nat.mul_div_cancel' eDivides]⟩

theorem norm_induced_gauss_term {M d e : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    (eMember : e ∈ M.divisors) (k : ℕ) {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) :
    ‖moebiusComplex e * χ (e : ZMod d) *
        (∑ v ∈ range (M / e), χ (v : ZMod d) *
          BombieriVinogradov.LargeSieve.additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ)))‖ ≤
      if e.Coprime d ∧ (M / e / d) ∣ k then ((M / e / d : ℕ) : ℝ) * Real.sqrt d else 0 := by
  by_cases coprime : e.Coprime d
  · obtain ⟨fPositive, hFactor, _⟩ := conductor_cofactor dDivides eMember coprime
    let f := M / e / d
    letI : NeZero f := ⟨fPositive.ne'⟩
    have liftIdentity : (∑ v ∈ range (M / e), χ (v : ZMod d) *
        BombieriVinogradov.LargeSieve.additivePhase ((k : ℝ) * v / ((M / e : ℕ) : ℝ))) =
        if f ∣ k then (f : ℂ) * gaussSum χ (ZMod.stdAddChar.mulShift ((k / f : ℕ) : ZMod d)) else 0 := by
      convert lift_gaussSum (f := f) χ k using 1
      rw [show (M / e : ℕ) = d * f from hFactor.symm, Nat.cast_mul]
    rw [liftIdentity]
    by_cases divides : f ∣ k
    · have divides' : (M / e / d) ∣ k := divides
      have relevant : e.Coprime d ∧ (M / e / d) ∣ k := ⟨coprime, divides'⟩
      simp only [if_pos divides, if_pos relevant, norm_mul, Complex.norm_natCast]
      have factor : ‖moebiusComplex e‖ * ‖χ (e : ZMod d)‖ ≤ 1 := by
        exact (mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)).trans
          (by simpa only [mul_one] using norm_moebiusComplex_le_one e)
      refine (mul_le_of_le_one_left (by positivity) factor).trans ?_
      exact mul_le_mul_of_nonneg_left (norm_primitive_gauss_shift_le primitive _) (Nat.cast_nonneg _)
    · have divides' : ¬(M / e / d) ∣ k := divides
      simp [divides, divides', coprime]
  · have valZero : χ (e : ZMod d) = 0 := MulChar.map_nonunit _
      (fun h => coprime ((ZMod.isUnit_iff_coprime e d).mp h))
    simp [coprime, valZero]

theorem norm_induced_gauss_le {M d : ℕ} [NeZero M] [NeZero d] (dDivides : d ∣ M)
    {χ : DirichletCharacter ℂ d} (primitive : χ.IsPrimitive) (k : ℕ) (kPositive : 0 < k) :
    ‖gaussSum (DirichletCharacter.changeLevel dDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod M))‖ ≤
      Real.sqrt d * ∑ f ∈ k.divisors.filter (fun f => d * f ∣ M), (f : ℝ) := by
  let cof (e : ℕ) := M / e / d
  let support := M.divisors.filter (fun e => e.Coprime d ∧ cof e ∣ k)
  let bound := k.divisors.filter (fun f => d * f ∣ M)
  have imageSubset : support.image cof ⊆ bound := by
    intro f member
    obtain ⟨e, eMember, rfl⟩ := mem_image.mp member
    obtain ⟨divisor, coprime, divides⟩ := mem_filter.mp eMember
    obtain ⟨_, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨divides, kPositive.ne'⟩,
      ⟨e, by rw [mul_comm]; exact identity.symm⟩⟩
  have injectiveOn : Set.InjOn cof (support : Set ℕ) := by
    intro e eMember e' e'Member same
    obtain ⟨divisor, coprime, _⟩ := mem_filter.mp eMember
    obtain ⟨divisor', coprime', _⟩ := mem_filter.mp e'Member
    obtain ⟨fPositive, _, identity⟩ := conductor_cofactor dDivides divisor coprime
    obtain ⟨_, _, identity'⟩ := conductor_cofactor dDivides divisor' coprime'
    change e * (d * cof e) = M at identity
    change e' * (d * cof e') = M at identity'
    rw [← same] at identity'
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (NeZero.pos d) fPositive) (identity.trans identity'.symm)
  have sumBound : (∑ e ∈ support, (cof e : ℝ)) ≤ ∑ f ∈ bound, (f : ℝ) := by
    rw [← sum_image injectiveOn]
    exact sum_le_sum_of_subset_of_nonneg imageSubset fun _ _ _ => Nat.cast_nonneg _
  rw [sum_inducedGauss_moebius]
  refine (norm_sum_le _ _).trans ?_
  have boundTerms := sum_le_sum (s := M.divisors)
    (fun e member => norm_induced_gauss_term dDivides member k primitive)
  refine boundTerms.trans ?_
  change (∑ e ∈ M.divisors, if e.Coprime d ∧ cof e ∣ k then (cof e : ℝ) * Real.sqrt d else 0) ≤
    Real.sqrt d * ∑ f ∈ bound, (f : ℝ)
  rw [← sum_filter, ← sum_mul, mul_comm (Real.sqrt d)]
  exact mul_le_mul_of_nonneg_right sumBound (Real.sqrt_nonneg _)


end
end DyadicMixedB4ImprimitiveBound

end

open Finset DyadicMixedB4ImprimitiveBound
namespace DyadicMixedB4CharacterFactorBound
noncomputable section
theorem norm_dirichlet_gauss_induced {r q : ℕ} [NeZero r] [NeZero q] (rDivides : r ∣ q)
    (χ : DirichletCharacter ℂ r) (k : ℕ) (kPositive : 0 < k) :
    ‖gaussSum (DirichletCharacter.changeLevel rDivides χ) (ZMod.stdAddChar.mulShift (k : ZMod q))‖ ≤
      Real.sqrt χ.conductor * ∑ f ∈ k.divisors.filter (fun f => χ.conductor * f ∣ q), (f : ℝ) := by
  have conductorNonzero : χ.conductor ≠ 0 := fun zero => NeZero.ne r
    (DirichletCharacter.conductor_eq_zero_iff_level_eq_zero.mp zero)
  letI : NeZero χ.conductor := ⟨conductorNonzero⟩
  have inductionBound := norm_induced_gauss_le (χ.conductor_dvd_level.trans rDivides)
    χ.primitiveCharacter_isPrimitive k kPositive
  rw [DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level rDivides,
    DirichletCharacter.changeLevel_primitiveCharacter] at inductionBound
  exact inductionBound

theorem norm_dirichlet_gauss_standard {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ Real.sqrt χ.conductor := by
  have induced := norm_dirichlet_gauss_induced (dvd_refl r) χ 1 (by decide)
  have onlyOne : ((1 : ℕ).divisors.filter (fun f => χ.conductor * f ∣ r)) = {1} := by
    ext f
    simp only [Nat.divisors_one, mem_filter, mem_singleton]
    constructor
    · exact And.left
    · rintro rfl
      exact ⟨rfl, by simpa only [mul_one] using χ.conductor_dvd_level⟩
  rw [onlyOne] at induced
  simpa [DirichletCharacter.changeLevel_self, AddChar.mulShift_one] using induced

end
end DyadicMixedB4CharacterFactorBound

namespace InnerFloorGaussPacket
open Finset AddChar Complex
open scoped Classical ComplexConjugate
open DyadicMixedB4CharacterFactorBound
noncomputable section
set_option maxHeartbeats 2000000
variable {q : ℕ} [NeZero q]

/-- The exact additiveWeight used in the accepted canonical zero correction. -/
def canonicalWeight (a : ZMod q) (χ : DirichletCharacter ℂ q) : ℂ :=
  conj (∑ r : ZMod q, conj (ZMod.stdAddChar (a*r))*χ r) / (q.totient:ℂ)

theorem canonicalWeight_eq (a : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    canonicalWeight (a:ZMod q) χ =
      χ (a:ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar / (q.totient:ℂ) := by
  unfold canonicalWeight
  have he : conj (∑ r : ZMod q, conj (ZMod.stdAddChar ((a:ZMod q)*r))*χ r) =
      gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (a:ZMod q)) := by
    rw [map_sum,gaussSum]
    apply sum_congr rfl
    intro r _
    rw [map_mul]
    change star (star (ZMod.stdAddChar ((a:ZMod q)*r))) * star (χ r) = _
    rw [star_star,MulChar.star_apply',AddChar.mulShift_apply,mul_comm]
  rw [he,gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar a,inv_inv]

theorem canonicalWeight_norm (a : (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    ‖canonicalWeight (a:ZMod q) χ‖ ≤ Real.sqrt χ.conductor/(q.totient:ℝ) := by
  rw [canonicalWeight_eq,norm_div,norm_mul,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := norm_dirichlet_gauss_standard χ⁻¹
  rw [DirichletCharacter.conductor_inv] at h
  exact (mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)).trans h

/-- Signed coefficient at an arbitrary real shift. A phase need only have
norm at most one; no independence or favourable sign is assumed. -/
def canonicalPairCoefficient (χ ψ : DirichletCharacter ℂ q)
    (phase : (ZMod q)ˣ → ℂ) : ℂ :=
  ∑ a : (ZMod q)ˣ, canonicalWeight (a:ZMod q) χ *
    canonicalWeight (a:ZMod q) ψ * phase a

theorem canonicalPairCoefficient_bound (χ ψ : DirichletCharacter ℂ q)
    (phase : (ZMod q)ˣ → ℂ) (hp : ∀ a, ‖phase a‖ ≤ 1) :
    ‖canonicalPairCoefficient χ ψ phase‖ ≤
      Real.sqrt χ.conductor * Real.sqrt ψ.conductor / (q.totient:ℝ) := by
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  unfold canonicalPairCoefficient
  calc
    _ ≤ ∑ a : (ZMod q)ˣ, ‖canonicalWeight (a:ZMod q) χ *
        canonicalWeight (a:ZMod q) ψ * phase a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod q)ˣ,
        (Real.sqrt χ.conductor/(q.totient:ℝ))*
        (Real.sqrt ψ.conductor/(q.totient:ℝ)) := by
      apply sum_le_sum
      intro a _
      rw [norm_mul,norm_mul]
      calc
        _ ≤ ‖canonicalWeight (a:ZMod q) χ‖ * ‖canonicalWeight (a:ZMod q) ψ‖ :=
          mul_le_of_le_one_right (by positivity) (hp a)
        _ ≤ _ := mul_le_mul (canonicalWeight_norm a χ) (canonicalWeight_norm a ψ)
          (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [sum_const,Finset.card_univ,ZMod.card_units_eq_totient,nsmul_eq_mul]
      field_simp

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.canonicalWeight_eq
#print axioms InnerFloorGaussPacket.canonicalWeight_norm
#print axioms InnerFloorGaussPacket.canonicalPairCoefficient_bound

namespace InnerFloorGaussPacket
open Finset AddChar Complex InnerFloorLinearTotient InnerFloorZeroModel
open scoped Classical ComplexConjugate
noncomputable section
set_option maxHeartbeats 2000000

variable {q : ℕ} [NeZero q]

theorem signedPair_eq (χ ψ : DirichletCharacter ℂ q) (n : ZMod q) :
    canonicalPairCoefficient χ ψ
      (fun a => ZMod.stdAddChar (-n*(a:ZMod q))) =
      (gaussSum χ⁻¹ ZMod.stdAddChar * gaussSum ψ⁻¹ ZMod.stdAddChar /
        (q.totient:ℂ)^2) *
        gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-n)) := by
  have hφ : (q.totient:ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  unfold canonicalPairCoefficient
  simp_rw [canonicalWeight_eq]
  have ht (a : (ZMod q)ˣ) :
      (χ (a:ZMod q)*gaussSum χ⁻¹ ZMod.stdAddChar/(q.totient:ℂ)) *
        (ψ (a:ZMod q)*gaussSum ψ⁻¹ ZMod.stdAddChar/(q.totient:ℂ)) *
          ZMod.stdAddChar (-n*(a:ZMod q)) =
      (gaussSum χ⁻¹ ZMod.stdAddChar * gaussSum ψ⁻¹ ZMod.stdAddChar /
        (q.totient:ℂ)^2) *
        ((χ*ψ) (a:ZMod q)*ZMod.stdAddChar (-n*(a:ZMod q))) := by
    rw [MulChar.mul_apply]
    field_simp
    <;> ring
  simp_rw [ht,← Finset.mul_sum]
  congr 1
  let F : ZMod q → ℂ := fun a => (χ*ψ) a * ZMod.stdAddChar (-n*a)
  change (∑ a : (ZMod q)ˣ, F (a:ZMod q)) = ∑ a : ZMod q, F a
  let S := (Finset.univ : Finset (ZMod q)).filter IsUnit
  have hS : (∑ a : (ZMod q)ˣ, F (a:ZMod q)) = ∑ a∈S, F a := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (ZMod q)ˣ))
      (t := S) (fun a _ => (a : ZMod q))
    · intro a _
      simp [S,a.isUnit]
    · intro a _ b _ h
      exact Units.ext h
    · intro a ha
      have hu : IsUnit a := by simpa [S] using ha
      exact ⟨hu.unit,Finset.mem_univ _,hu.unit_spec⟩
    · intro a _
      rfl
  rw [hS]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro a ha hnot
  have hn : ¬ IsUnit a := by simpa [S] using hnot
  dsimp [F]
  simp [MulChar.map_nonunit _ hn]

/-- The common modulus is a multiple of the LCM of the primitive levels.
All coefficients are those of the actual finite additiveWeight expansion. -/
theorem liftedContinuousPacket_bound {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    (χ : DirichletCharacter ℂ d₁) (ψ : DirichletCharacter ℂ d₂)
    (L M : ℕ) (hL : 0 < L) (h₁ : d₁∣L) (h₂ : d₂∣L)
    (S : Finset ℕ) (hS : S ⊆ Icc 1 M)
    (U X β₁ γ₁ β₂ γ₂ : ℝ) (hU : 0≤U) (hX : 0≤X)
    (hβ₁ : 1/2≤β₁) (hβ₂ : 1/2≤β₂) (n : ℕ) :
    let a (m : ℕ) : ℂ :=
      if hm : 0 < m then
        letI : NeZero (L*m) := ⟨(Nat.mul_pos hL hm).ne'⟩
        canonicalPairCoefficient
          (DirichletCharacter.changeLevel (h₁.trans (dvd_mul_right L m)) χ)
          (DirichletCharacter.changeLevel (h₂.trans (dvd_mul_right L m)) ψ)
          (fun a => ZMod.stdAddChar (-(n:ZMod (L*m))*(a:ZMod (L*m))))
      else 0
    ‖(X:ℂ)*(∑ m∈S, a m * pairIntegral β₁ γ₁ β₂ γ₂ (U/((L*m:ℕ):ℝ)))‖ ≤
      8*exceptionalWeightConstant*X*U/(L.totient:ℝ) := by
  dsimp only
  let g := Real.sqrt (d₁:ℝ)*Real.sqrt (d₂:ℝ)
  have hg : 0≤g := by dsimp [g]; positivity
  have hgL : g≤(L:ℝ) := by
    calc
      g ≤ Real.sqrt (L:ℝ)*Real.sqrt (L:ℝ) :=
        mul_le_mul
          (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd hL h₁))
          (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd hL h₂))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  apply continuousPacket_bound S M L hL hS g U X β₁ γ₁ β₂ γ₂ hg hgL hU hX hβ₁ hβ₂
  intro m hm
  have hm0 : 0 < m := (mem_Icc.mp (hS hm)).1
  rw [dif_pos hm0]
  letI : NeZero (L*m) := ⟨(Nat.mul_pos hL hm0).ne'⟩
  have h := canonicalPairCoefficient_bound
    (DirichletCharacter.changeLevel (h₁.trans (dvd_mul_right L m)) χ)
    (DirichletCharacter.changeLevel (h₂.trans (dvd_mul_right L m)) ψ)
    (fun a => ZMod.stdAddChar (-(n:ZMod (L*m))*(a:ZMod (L*m))))
    (fun a => by
      have hu := AddChar.norm_apply (ZMod.stdAddChar (N := L*m))
        (-(n:ZMod (L*m))*(a:ZMod (L*m)))
      exact hu.le)
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel] at h
  apply h.trans
  unfold g
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (NeZero.pos d₁) χ.conductor_dvd_level))
    (Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd (NeZero.pos d₂) ψ.conductor_dvd_level))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.signedPair_eq
#print axioms InnerFloorGaussPacket.liftedContinuousPacket_bound
/-! Plancherel bridge adapted from ShortProgressionsMeanTheta (#3789),
and the verified InnerFloorPhysicalL2 research module. -/
section
open Set MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform ContDiff BigOperators Interval
namespace InnerFloorZeroModel
noncomputable section
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in


private theorem test_fourier_swap {f : ℝ → ℂ} (hf : Integrable f) (g : 𝓢(ℝ, ℂ)) :
    (∫ x, (𝓕 f) x • g x) = ∫ x, f x • (𝓕 g) x := by
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf g.integrable
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem ae_eq_of_schwartz_test {u v : ℝ → ℂ}
    (hu : LocallyIntegrable u volume) (hv : LocallyIntegrable v volume)
    (h : ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * u x) = ∫ x, φ x * v x) :
    u =ᵐ[volume] v := by
  apply ae_eq_of_integral_contDiff_smul_eq hu hv
  intro g hg hgc
  let φ := (hgc.comp_left (show Complex.ofRealCLM 0 = 0 by simp)).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) by fun_prop)
  simp only [RCLike.real_smul_eq_coe_mul]
  exact h φ
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem lp_test (v : Lp ℂ 2 (volume : Measure ℝ)) (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, (𝓕 φ) x • v x) = ∫ x, φ x • (𝓕 v) x := calc
  _ = Lp.toTemperedDistribution v (𝓕 φ) := (Lp.toTemperedDistribution_apply ..).symm
  _ = (𝓕 (Lp.toTemperedDistribution v)) φ := rfl
  _ = Lp.toTemperedDistribution (𝓕 v) φ := by rw [Lp.fourier_toTemperedDistribution_eq]
  _ = _ := Lp.toTemperedDistribution_apply ..
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem fourier_agrees {f : ℝ → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (𝓕 f) =ᵐ[volume] (𝓕 (h₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  let v := h₂.toLp f
  have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ h₁
  apply ae_eq_of_schwartz_test hc.locallyIntegrable
    ((Lp.memLp (𝓕 v)).locallyIntegrable (by norm_num))
  intro φ
  have A := test_fourier_swap (f := f) h₁ φ
  have B := lp_test v φ
  simp only [smul_eq_mul] at A B
  have C : (∫ x : ℝ, f x * (𝓕 φ) x) = ∫ x : ℝ, (𝓕 φ) x * v x := by
    apply integral_congr_ae
    filter_upwards [h₂.coeFn_toLp] with x hx
    change f x * (𝓕 φ) x = (𝓕 φ) x * (h₂.toLp f) x
    rw [hx, mul_comm]
  have D : (∫ x : ℝ, φ x * (𝓕 f) x) = ∫ x : ℝ, (𝓕 f) x * φ x :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm ..)
  exact D.trans (A.trans (C.trans B))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem lp_energy (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫ x, ‖f x‖^2 = ‖f‖^2 := by
  conv_rhs => rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)]
  exact integral_congr_ae (ae_of_all _ fun x => norm_sq_eq_re_inner (𝕜 := ℂ) (f x))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in

private theorem box_plancherel {f : ℝ → ℂ} (h₁ : Integrable f) (h₂ : MemLp f 2) :
    Integrable (fun ξ => ‖𝓕 f ξ‖^2) ∧ (∫ ξ, ‖𝓕 f ξ‖^2) = ∫ x, ‖f x‖^2 := by
  let v := h₂.toLp f
  have he := fourier_agrees h₁ h₂
  have hae : (fun ξ => ‖𝓕 f ξ‖^2) =ᵐ[volume] (fun ξ => ‖(𝓕 v) ξ‖^2) := by
    filter_upwards [he] with ξ h using congrArg (fun z : ℂ => ‖z‖^2) h
  refine ⟨((Lp.memLp (𝓕 v)).norm.integrable_sq).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, lp_energy, Lp.norm_fourier_eq, ← lp_energy]
  apply integral_congr_ae
  filter_upwards [h₂.coeFn_toLp] with x h using congrArg (fun z : ℂ => ‖z‖^2) h

def zeroKernel (β γ : ℝ) : ℝ → ℂ :=
  (Set.Ioc (0:ℝ) 1).indicator (fun x => (x^(β-1):ℝ) • phase (γ*Real.log x))

private theorem kernel_norm_eq (β γ : ℝ) :
    (fun x => ‖zeroKernel β γ x‖) =
      (Set.Ioc (0:ℝ) 1).indicator (fun x => x^(β-1)) := by
  funext x
  by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
  · rw [zeroKernel,Set.indicator_of_mem hx,Set.indicator_of_mem hx,norm_smul,norm_phase,
      mul_one,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
  · simp [zeroKernel,Set.indicator_of_notMem hx]

private theorem kernel_sq_eq (β γ : ℝ) :
    (fun x => ‖zeroKernel β γ x‖^2) =
      (Set.Ioc (0:ℝ) 1).indicator (fun x => x^(2*β-2)) := by
  funext x
  have hn := congrFun (kernel_norm_eq β γ) x
  rw [hn]
  by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
  · rw [Set.indicator_of_mem hx,Set.indicator_of_mem hx,
      ← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
    congr 1
    norm_num
    ring
  · simp [Set.indicator_of_notMem hx]

private theorem kernel_integrable (β γ : ℝ) (hβ : 0 < β) :
    Integrable (zeroKernel β γ) := by
  have hm : Measurable (zeroKernel β γ) := by
    unfold zeroKernel
    apply Measurable.indicator _ measurableSet_Ioc
    unfold phase
    fun_prop
  apply (integrable_norm_iff hm.aestronglyMeasurable).mp
  rw [kernel_norm_eq,integrable_indicator_iff measurableSet_Ioc]
  exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < β-1)).1

private theorem kernel_memLp (β γ : ℝ) (hβ : 1/2 < β) :
    MemLp (zeroKernel β γ) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (kernel_integrable β γ (by linarith)).aestronglyMeasurable).mpr
  rw [kernel_sq_eq,integrable_indicator_iff measurableSet_Ioc]
  exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 2*β-2)).1

private theorem kernel_energy (β γ : ℝ) (hβ : 1/2 < β) :
    ∫ x, ‖zeroKernel β γ x‖^2 = 1/(2*β-1) := by
  rw [kernel_sq_eq,integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num),
    integral_rpow (Or.inl (by linarith : -1 < 2*β-2))]
  rw [show 2*β-2+1=2*β-1 by ring,Real.one_rpow,
    Real.zero_rpow (by linarith : 2*β-1≠0),sub_zero]

private theorem transform_fourier (β γ v : ℝ) :
    transform β γ v = 𝓕 (zeroKernel β γ) (-v) := by
  rw [Real.fourier_real_eq_integral_exp_smul,transform,
    intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]
  have he : (fun x => Complex.exp (↑(-2*Real.pi*x*(-v))*Complex.I) • zeroKernel β γ x) =
    (Set.Ioc (0:ℝ) 1).indicator (fun x => (x^(β-1):ℝ) • phase (γ*Real.log x+2*Real.pi*v*x)) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (0:ℝ) 1
    · rw [zeroKernel,Set.indicator_of_mem hx,Set.indicator_of_mem hx]
      simp only [smul_eq_mul,phase,Complex.ofReal_add,add_mul,Complex.exp_add,
        RCLike.real_smul_eq_coe_mul]
      rw [show (-2*Real.pi*x*(-v)) = 2*Real.pi*v*x by ring]
      ring
    · simp [zeroKernel,Set.indicator_of_notMem hx]
  rw [he,integral_indicator measurableSet_Ioc]

theorem transform_energy (β γ : ℝ) (hβ : 1/2 < β) :
    Integrable (fun v => ‖transform β γ v‖^2) ∧
      (∫ v, ‖transform β γ v‖^2) = 1/(2*β-1) := by
  obtain ⟨hi,he⟩ := box_plancherel (kernel_integrable β γ (by linarith))
    (kernel_memLp β γ hβ)
  simp_rw [transform_fourier]
  constructor
  · simpa only [neg_one_mul] using hi.comp_mul_left' (by norm_num : (-1:ℝ)≠0)
  · calc
      _ = (∫ v, ‖𝓕 (zeroKernel β γ) v‖^2) := by
        have h := Measure.integral_comp_mul_left (fun v => ‖𝓕 (zeroKernel β γ) v‖^2) (-1:ℝ)
        simpa [neg_one_mul] using h
      _ = _ := he.trans (kernel_energy β γ hβ)


/-- The absolute integral of a pair is uniformly bounded at every cutoff,
including the long inner arcs. No hypothesis on the imaginary parts. -/
theorem pairIntegral_uniform (β₁ γ₁ β₂ γ₂ R : ℝ)
    (h₁ : 3/4≤β₁) (h₂ : 3/4≤β₂) (hR : 0≤R) :
    ‖pairIntegral β₁ γ₁ β₂ γ₂ R‖ ≤ 2 := by
  obtain ⟨hi₁,he₁⟩ := transform_energy β₁ γ₁ (by linarith)
  obtain ⟨hi₂,he₂⟩ := transform_energy β₂ γ₂ (by linarith)
  let f (v : ℝ) := (‖transform β₁ γ₁ v‖^2+‖transform β₂ γ₂ v‖^2)/2
  have hf : Integrable f := (hi₁.add hi₂).div_const 2
  have hp (v : ℝ) :
      ‖transform β₁ γ₁ v * transform β₂ γ₂ v * phase (-(2*Real.pi*v))‖ ≤ f v := by
    rw [norm_mul,norm_mul,norm_phase,mul_one]
    dsimp [f]
    nlinarith [sq_nonneg (‖transform β₁ γ₁ v‖-‖transform β₂ γ₂ v‖)]
  have hA : ∀ v, 0≤f v := by intro v;dsimp [f];positivity
  unfold pairIntegral
  rw [intervalIntegral.integral_of_le (by linarith : -R≤R)]
  calc
    _ ≤ ∫ v in Ioc (-R) R,
      ‖transform β₁ γ₁ v * transform β₂ γ₂ v * phase (-(2*Real.pi*v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioc (-R) R, f v :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hf.integrableOn (Filter.Eventually.of_forall hp)
    _ ≤ ∫ v, f v := setIntegral_le_integral hf (Filter.Eventually.of_forall hA)
    _ = (1/(2*β₁-1)+1/(2*β₂-1))/2 := by
      dsimp [f]
      rw [integral_div,integral_add hi₁ hi₂,he₁,he₂]
    _ ≤ 2 := by
      have hb₁ : 1/(2*β₁-1) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
      have hb₂ : 1/(2*β₂-1) ≤ 2 := (div_le_iff₀ (by linarith)).2 (by linarith)
      linarith

end
end InnerFloorZeroModel
#print axioms InnerFloorZeroModel.transform_energy

#print axioms InnerFloorZeroModel.pairIntegral_uniform
end

namespace DyadicMixedB4CharacterFactorBound
noncomputable section
theorem norm_gauss_neg_shift_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ZMod q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-x))‖ ≤ ‖gaussSum χ (ZMod.stdAddChar.mulShift x)‖ := by
  have equality : ZMod.stdAddChar.mulShift (-x) =
      (ZMod.stdAddChar.mulShift x).mulShift ((-1 : (ZMod q)ˣ) : ZMod q) := by
    ext y
    simp [AddChar.mulShift_apply, mul_assoc]
  rw [equality, gaussSum_mulShift_eq χ (ZMod.stdAddChar.mulShift x) (-1), norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)


end
end DyadicMixedB4CharacterFactorBound

open InnerFloorLinearTotient

/-!
A product-conductor saving for arbitrary shifts, including noncoprime
shifts. The low-product-conductor packet is kept separate.
-/
open Finset
open scoped Classical
open DyadicMixedB4CharacterFactorBound
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

theorem divisorSum_le_log (m : ℕ) (hm : 0 < m) :
    (∑ f ∈ m.divisors, (f:ℝ)) ≤ (m:ℝ)*(1+Real.log m) := by
  have hsub : m.divisors ⊆ Icc 1 m := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd)⟩
  have hh : (∑ i∈Icc 1 m,(i:ℝ)⁻¹) ≤ 1+Real.log m := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      using harmonic_le_one_add_log m
  calc
    _ = ∑ ab∈m.divisorsAntidiagonal,(ab.1:ℝ) := by
      rw [Nat.sum_divisorsAntidiagonal (fun a _ => (a:ℝ))]
    _ = ∑ ab∈m.divisorsAntidiagonal,(m:ℝ)*(ab.2:ℝ)⁻¹ := by
      apply sum_congr rfl
      intro ab hab
      have hp := (Nat.mem_divisorsAntidiagonal.mp hab).1
      have hb : ab.2 ≠ 0 := by
        intro hb
        rw [hb,mul_zero] at hp
        omega
      have he : (ab.1:ℝ)*(ab.2:ℝ)=(m:ℝ) := by exact_mod_cast hp
      rw [← he]
      field_simp
    _ = (m:ℝ)*(∑ f∈m.divisors,(f:ℝ)⁻¹) := by
      rw [← mul_sum,Nat.sum_divisorsAntidiagonal' (fun _ b => (b:ℝ)⁻¹)]
    _ ≤ (m:ℝ)*(∑ f∈Icc 1 m,(f:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)

variable {q : ℕ} [NeZero q]

/-- Even when the shift is not invertible modulo q, the shifted Gauss sum
is at most q (1+log q) / sqrt(conductor). -/
theorem shiftedGauss_productConductor (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : 0 < n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*(1+Real.log q)/Real.sqrt χ.conductor := by
  let d := χ.conductor
  have hd : d ∣ q := χ.conductor_dvd_level
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd (NeZero.pos q)
  obtain ⟨m,hm⟩ := hd
  have hmp : 0 < m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm0,mul_zero] at hm
    exact (NeZero.ne q) hm
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hdp
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hmp
  have hqR : (q:ℝ)=(d:ℝ)*(m:ℝ) := by exact_mod_cast hm
  have hsub : n.divisors.filter (fun f => d*f ∣ q) ⊆ m.divisors := by
    intro f hf
    have hdiv := (mem_filter.mp hf).2
    rw [hm] at hdiv
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left hdp hdiv,hmp.ne'⟩
  have hmq : m ≤ q := by
    rw [hm]
    exact Nat.le_mul_of_pos_left _ hdp
  have hlog : Real.log m≤Real.log q :=
    Real.log_le_log hmR (by exact_mod_cast hmq)
  have hs : (Real.sqrt (d:ℝ))^2=(d:ℝ) := Real.sq_sqrt hdR.le
  have hroot : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.2 hdR
  calc
    _ ≤ Real.sqrt d*(∑ f∈n.divisors.filter (fun f => d*f ∣ q),(f:ℝ)) :=
      (norm_gauss_neg_shift_le χ (n:ZMod q)).trans
        (by simpa only [DirichletCharacter.changeLevel_self,d] using
          norm_dirichlet_gauss_induced (dvd_refl q) χ n hn)
    _ ≤ Real.sqrt d*(∑ f∈m.divisors,(f:ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt d*((m:ℝ)*(1+Real.log m)) :=
      mul_le_mul_of_nonneg_left (divisorSum_le_log m hmp) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt d*((m:ℝ)*(1+Real.log q)) := by gcongr
    _ = _ := by
      change Real.sqrt (d:ℝ)*((m:ℝ)*(1+Real.log q)) =
        (q:ℝ)*(1+Real.log q)/Real.sqrt (d:ℝ)
      apply (eq_div_iff hroot.ne').2
      calc
        _ = (Real.sqrt (d:ℝ))^2 * ((m:ℝ)*(1+Real.log q)) := by ring
        _ = (d:ℝ)*((m:ℝ)*(1+Real.log q)) := by rw [hs]
        _ = _ := by rw [hqR]; ring

/-- The high-product-conductor part of the signed quadratic form has a
uniform square-root saving, independent of gcd(n,q). -/
theorem highProductConductorPacketBound
    (n : ℕ) (hn : 0 < n) (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) (D : ℕ) (hD : 0 < D) :
    ‖∑ χ∈S, ∑ ψ∈S.filter (fun ψ => D≤(χ*ψ).conductor),
       (w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      ((q:ℝ)*(1+Real.log q)/Real.sqrt D)*(∑ χ∈S,‖w χ‖)^2 := by
  let K := (q:ℝ)*(1+Real.log q)/Real.sqrt D
  have hq1 : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hL : 0≤(q:ℝ)*(1+Real.log q) := by
    have := Real.log_nonneg hq1
    positivity
  have hK : 0≤K := div_nonneg hL (Real.sqrt_nonneg _)
  have hterm (χ ψ : DirichletCharacter ℂ q) (hψ : D≤(χ*ψ).conductor) :
      ‖(w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
        ‖w χ‖*‖w ψ‖*K := by
    simp only [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply (shiftedGauss_productConductor (χ*ψ) n hn).trans
    exact div_le_div_of_nonneg_left hL (Real.sqrt_pos.2 (by exact_mod_cast hD))
      (Real.sqrt_le_sqrt (by exact_mod_cast hψ))
  change _ ≤ K*(∑ χ∈S,‖w χ‖)^2
  calc
    _ ≤ ∑ χ∈S, ∑ ψ∈S.filter (fun ψ => D≤(χ*ψ).conductor), ‖w χ‖*‖w ψ‖*K := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro χ _
      apply (norm_sum_le _ _).trans
      exact sum_le_sum fun ψ hψ => hterm χ ψ (mem_filter.mp hψ).2
    _ ≤ ∑ χ∈S, ∑ ψ∈S, ‖w χ‖*‖w ψ‖*K :=
      sum_le_sum fun χ _ => sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = _ := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

end
end InnerFloorResearch

open InnerFloorLinearTotient

/-!
Aggregate high-product-conductor weights over all common multiples.
Only finite arithmetic and the verified Gauss bound are used.
-/
open Finset InnerFloorLinearTotient
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1500000

theorem commonMultipleTotientWeight (A L : ℕ) (hL : 0 < L) (hLA : L ≤ A) :
    (∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) ≤
      (weightConstant*(1+Real.log A))^2 := by
  let F (d : ℕ) : ℝ := if d=L then L else 0
  have hF : ∀ d, 0≤F d := by intro d; dsimp [F]; split_ifs <;> positivity
  have hA : 0 < A := hL.trans_le hLA
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg (by exact_mod_cast hA)
  have hlogL : Real.log L ≤ Real.log A :=
    Real.log_le_log (by exact_mod_cast hL) (by exact_mod_cast hLA)
  have hLf : L ∈ Icc 1 A := mem_Icc.mpr ⟨hL,hLA⟩
  have hratio : (L:ℝ)/(L.totient:ℝ) ≤ weightConstant*(1+Real.log A) :=
    (ratio_totient_le L hL).trans (mul_le_mul_of_nonneg_left (by linarith)
      weightConstant_nonneg)
  have hrewrite :
      (∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) =
      ∑ q ∈ Icc 1 A, (∑ d ∈ q.divisors,F d)/(q.totient:ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro q hq
    have hq0 : q ≠ 0 := by have := (mem_Icc.mp hq).1; omega
    have hmem : L ∈ q.divisors ↔ L ∣ q := by simp [Nat.mem_divisors,hq0]
    by_cases hdiv : L ∣ q
    · have h := hmem.mpr hdiv
      simp [F,hdiv,h]
    · have h : L ∉ q.divisors := fun hm => hdiv (hmem.mp hm)
      simp [F,hdiv,h]
  have hsum : (∑ d ∈ Icc 1 A,F d/(d.totient:ℝ)) = (L:ℝ)/(L.totient:ℝ) := by
    simp [F,ite_div,hLf]
  rw [hrewrite]
  apply (sum_conductor_weights A F hF).trans
  rw [hsum,pow_two]
  exact mul_le_mul_of_nonneg_right hratio (mul_nonneg weightConstant_nonneg (by linarith))

def productCoefficient (q d₁ d₂ D : ℕ) : ℝ :=
  Real.sqrt d₁ * Real.sqrt d₂ * q * (1+Real.log q) /
    ((q.totient:ℝ)^2 * Real.sqrt D)

/-- At most four logarithms are lost when summing the high-product
conductor coefficient over all moduli divisible by both original
conductors. No assumption on gcd(n,q) occurs. -/
theorem productCoefficientFamily (A d₁ d₂ D : ℕ)
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) (hD : 0 < D) :
    (∑ q ∈ (Icc 1 A).filter (fun q => d₁ ∣ q ∧ d₂ ∣ q),
       productCoefficient q d₁ d₂ D) ≤
      weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  let L := Nat.lcm d₁ d₂
  have hL : 0 < L := Nat.lcm_pos h₁ h₂
  have hset :
      (Icc 1 A).filter (fun q => d₁ ∣ q ∧ d₂ ∣ q) =
        (Icc 1 A).filter (fun q => L ∣ q) := by
    ext q
    simp [L,Nat.lcm_dvd_iff]
  have hD' : 0 < Real.sqrt (D:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hD)
  have hd₁ : d₁ ≤ L := Nat.le_of_dvd hL (Nat.dvd_lcm_left d₁ d₂)
  have hd₂ : d₂ ≤ L := Nat.le_of_dvd hL (Nat.dvd_lcm_right d₁ d₂)
  have hroot : Real.sqrt (d₁:ℝ)*Real.sqrt (d₂:ℝ) ≤ (L:ℝ) := by
    calc
      _ ≤ Real.sqrt (L:ℝ)*Real.sqrt (L:ℝ) :=
        mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hd₁))
          (Real.sqrt_le_sqrt (by exact_mod_cast hd₂)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  by_cases hLA : L≤A
  · have hA : 0 < A := hL.trans_le hLA
    have hlogA : 0≤Real.log A := Real.log_nonneg (by exact_mod_cast hA)
    let C := weightConstant*(1+Real.log A)^2/Real.sqrt D
    have hC : 0≤C := by
      dsimp [C]
      exact div_nonneg (mul_nonneg weightConstant_nonneg (sq_nonneg _)) (Real.sqrt_nonneg _)
    have ht (q : ℕ) (hq : q∈(Icc 1 A).filter (fun q => L ∣ q)) :
        productCoefficient q d₁ d₂ D ≤ C*((L:ℝ)/(q.totient:ℝ)) := by
      have hq1 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
      have hqA := (mem_Icc.mp (mem_filter.mp hq).1).2
      have hlogq : 0≤Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
      have hlog : Real.log q≤Real.log A :=
        Real.log_le_log (by exact_mod_cast hq1) (by exact_mod_cast hqA)
      have hφ : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
      have hr : (q:ℝ)/(q.totient:ℝ) ≤ weightConstant*(1+Real.log A) :=
        (ratio_totient_le q hq1).trans
          (mul_le_mul_of_nonneg_left (by linarith) weightConstant_nonneg)
      calc
        _ = (Real.sqrt (d₁:ℝ)*Real.sqrt (d₂:ℝ)/(q.totient:ℝ))*
            ((q:ℝ)/(q.totient:ℝ))*(1+Real.log q)/Real.sqrt D := by
          unfold productCoefficient
          ring
        _ ≤ ((L:ℝ)/(q.totient:ℝ))*(weightConstant*(1+Real.log A))*
            (1+Real.log A)/Real.sqrt D := by
          apply div_le_div_of_nonneg_right _ hD'.le
          apply mul_le_mul _ (by linarith) (by positivity)
            (mul_nonneg (by positivity) (mul_nonneg weightConstant_nonneg (by linarith)))
          exact mul_le_mul (div_le_div_of_nonneg_right hroot hφ.le) hr
            (by positivity) (by positivity)
        _ = _ := by dsimp [C]; ring
    rw [hset]
    calc
      _ ≤ ∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), C*((L:ℝ)/(q.totient:ℝ)) :=
        sum_le_sum ht
      _ = C*(∑ q ∈ (Icc 1 A).filter (fun q => L ∣ q), (L:ℝ)/(q.totient:ℝ)) :=
        (mul_sum ..).symm
      _ ≤ C*(weightConstant*(1+Real.log A))^2 :=
        mul_le_mul_of_nonneg_left (commonMultipleTotientWeight A L hL hLA) hC
      _ = _ := by dsimp [C]; ring
  · have he : (Icc 1 A).filter (fun q => L ∣ q)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hq' := mem_filter.mp hq
      exact hLA ((Nat.le_of_dvd (mem_Icc.mp hq'.1).1 hq'.2).trans (mem_Icc.mp hq'.1).2)
    rw [hset,he,sum_empty]
    exact div_nonneg (mul_nonneg (pow_nonneg weightConstant_nonneg _) (by positivity)) (Real.sqrt_nonneg _)

end
end InnerFloorResearch

open InnerFloorLinearTotient

/-!
Retain both the product conductor and the gcd of the shift with the
imprimitive part of the modulus. All estimates are unconditional.
-/
open Finset DyadicMixedB4CharacterFactorBound
open scoped Classical
namespace InnerFloorResearch
noncomputable section
set_option maxHeartbeats 1000000

variable {q : ℕ} [NeZero q]

theorem shiftedGauss_gcdBound (χ : DirichletCharacter ℂ q) (n : ℕ)
    (hn : 0 < n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      Real.sqrt χ.conductor * (Nat.gcd n (q/χ.conductor):ℝ) *
        (1+Real.log (Nat.gcd n (q/χ.conductor))) := by
  let d := χ.conductor
  have hd : d ∣ q := χ.conductor_dvd_level
  have hdp : 0 < d := Nat.pos_of_dvd_of_pos hd (NeZero.pos q)
  obtain ⟨m,hm⟩ := hd
  have hmp : 0 < m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm0,mul_zero] at hm
    exact (NeZero.ne q) hm
  have hm' : q/d=m := by
    rw [hm,Nat.mul_comm,Nat.mul_div_cancel _ hdp]
  let g := Nat.gcd n m
  have hgp : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have hsub : n.divisors.filter (fun f => d*f ∣ q) ⊆ g.divisors := by
    intro f hf
    have hdiv := (mem_filter.mp hf).2
    rw [hm] at hdiv
    have hfm := Nat.dvd_of_mul_dvd_mul_left hdp hdiv
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd
      (Nat.dvd_of_mem_divisors (mem_filter.mp hf).1) hfm,hgp.ne'⟩
  change _ ≤ Real.sqrt d * (Nat.gcd n (q/d):ℝ) * _
  rw [hm']
  calc
    _ ≤ Real.sqrt d*(∑ f∈n.divisors.filter (fun f => d*f ∣ q),(f:ℝ)) :=
      (norm_gauss_neg_shift_le χ (n:ZMod q)).trans
        (by simpa only [DirichletCharacter.changeLevel_self,d] using
          norm_dirichlet_gauss_induced (dvd_refl q) χ n hn)
    _ ≤ Real.sqrt d*(∑ f∈g.divisors,(f:ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => by positivity)) (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt d*((g:ℝ)*(1+Real.log g)) :=
      mul_le_mul_of_nonneg_left (divisorSum_le_log g hgp) (Real.sqrt_nonneg _)
    _ = _ := by dsimp [g,d]; ring

/-- A general bound using gcd(n,q) rather than the full modulus, useful
for small product conductor. -/
theorem shiftedGauss_smallProduct (χ : DirichletCharacter ℂ q) (n D : ℕ)
    (hn : 0 < n) (hD : χ.conductor ≤ D) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      Real.sqrt D*(Nat.gcd n q:ℝ)*(1+Real.log q) := by
  let g := Nat.gcd n (q/χ.conductor)
  have hgp : 0 < g := Nat.gcd_pos_of_pos_left _ hn
  have hgg : g ∣ Nat.gcd n q := Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    ((Nat.gcd_dvd_right _ _).trans (Nat.div_dvd_of_dvd χ.conductor_dvd_level))
  have hgq : g≤q := Nat.le_of_dvd (NeZero.pos q) (hgg.trans (Nat.gcd_dvd_right _ _))
  have hgg' : g≤Nat.gcd n q := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hn) hgg
  have hL : 0≤Real.log g := Real.log_nonneg (by exact_mod_cast hgp)
  have hl : Real.log (g:ℝ) ≤ Real.log (q:ℝ) :=
    Real.log_le_log (by exact_mod_cast hgp) (by exact_mod_cast hgq)
  calc
    _ ≤ Real.sqrt χ.conductor*(g:ℝ)*(1+Real.log g) :=
      shiftedGauss_gcdBound χ n hn
    _ ≤ _ := by
      apply mul_le_mul
      · exact mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hD))
          (by exact_mod_cast hgg' : (g:ℝ) ≤ (Nat.gcd n q:ℝ)) (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      · linarith
      · linarith
      · positivity

/-- The low-product-conductor part of a packet also has a saving when
gcd(n,q) is small. No coprimality assumption is necessary. -/
theorem lowProductGcdPacketBound (n : ℕ) (hn : 0 < n)
    (S : Finset (DirichletCharacter ℂ q))
    (w : DirichletCharacter ℂ q → ℂ) (D : ℕ) :
    ‖∑ χ∈S, ∑ ψ∈S.filter (fun ψ => (χ*ψ).conductor≤D),
        (w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (Real.sqrt D*(Nat.gcd n q:ℝ)*(1+Real.log q))*(∑ χ∈S,‖w χ‖)^2 := by
  let K := Real.sqrt D*(Nat.gcd n q:ℝ)*(1+Real.log q)
  have hq1 : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hK : 0≤K := by
    dsimp [K]
    have := Real.log_nonneg hq1
    positivity
  have hterm (χ ψ : DirichletCharacter ℂ q) (hψ : (χ*ψ).conductor≤D) :
      ‖(w χ*w ψ)*gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
        ‖w χ‖*‖w ψ‖*K := by
    simp only [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact shiftedGauss_smallProduct (χ*ψ) n D hn hψ
  change _ ≤ K*(∑ χ∈S,‖w χ‖)^2
  calc
    _ ≤ ∑ χ∈S, ∑ ψ∈S.filter (fun ψ => (χ*ψ).conductor≤D), ‖w χ‖*‖w ψ‖*K := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro χ _
      apply (norm_sum_le _ _).trans
      exact sum_le_sum fun ψ hψ => hterm χ ψ (mem_filter.mp hψ).2
    _ ≤ ∑ χ∈S, ∑ ψ∈S, ‖w χ‖*‖w ψ‖*K :=
      sum_le_sum fun χ _ => sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => by positivity)
    _ = _ := by
      simp_rw [← Finset.sum_mul,← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring


/-- Interpolating the product conductor and gcd bounds eliminates the
conductor altogether. The ratio gcd(n,q)/q is the precise obstruction. -/
theorem shiftedGauss_geometricGcd (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : 0 < n) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q) := by
  let d := χ.conductor
  have hd : 0 < d := Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos q)
  have hs : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hL : 0 ≤ 1+Real.log q := by
    have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
    linarith [Real.log_nonneg hq1]
  let a := ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖
  have ha : 0≤a := norm_nonneg _
  have h₁ : a ≤ (q:ℝ)*(1+Real.log q)/Real.sqrt d :=
    shiftedGauss_productConductor χ n hn
  have h₂ : a ≤ Real.sqrt d*(Nat.gcd n q:ℝ)*(1+Real.log q) :=
    shiftedGauss_smallProduct χ n d hn le_rfl
  have hsq : a^2 ≤ ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q)^2 := by
    calc
      _ = a*a := by ring
      _ ≤ ((q:ℝ)*(1+Real.log q)/Real.sqrt d)*
          (Real.sqrt d*(Nat.gcd n q:ℝ)*(1+Real.log q)) :=
        mul_le_mul h₁ h₂ ha (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hL) hs.le)
      _ = _ := by field_simp [hs.ne'] <;> ring
  have hroot : (Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ)))^2 =
      (q:ℝ)*(Nat.gcd n q:ℝ) := Real.sq_sqrt (by positivity)
  have hb : 0≤Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q) :=
    mul_nonneg (Real.sqrt_nonneg _) hL
  have hsq' : a^2 ≤ (Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ))*(1+Real.log q))^2 := by
    rw [mul_pow,hroot]
    exact hsq
  change a ≤ _
  nlinarith only [hsq',ha,hb]

/-- The fraction of a modulus accounted for by gcd(n,q) cannot increase
when q is replaced by a multiple. -/
theorem gcdRatio_mono_multiple (n L q : ℕ) (hn : 0 < n) (hL : 0 < L)
    (hLq : L ∣ q) (hq : 0 < q) :
    (Nat.gcd n q:ℝ)/(q:ℝ) ≤ (Nat.gcd n L:ℝ)/(L:ℝ) := by
  obtain ⟨m,hm⟩ := hLq
  have hmpos : 0 < m := by
    by_contra! h
    have hm0 : m=0 := by omega
    rw [hm,hm0,mul_zero] at hq
    omega
  let d := Nat.gcd n q
  have hd : d ∣ L*m := by rw [← hm]; exact Nat.gcd_dvd_right _ _
  have hsplit : d ∣ d.gcd L * d.gcd m := by
    simpa only [Nat.gcd_comm] using (Nat.dvd_gcd_mul_gcd_iff_dvd_mul.mpr hd)
  have h₁ : d.gcd L ∣ Nat.gcd n L :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left n q))
      (Nat.gcd_dvd_right _ _)
  have h₂ : d.gcd m ∣ m := Nat.gcd_dvd_right _ _
  have hdiv : d ∣ Nat.gcd n L*m := hsplit.trans (Nat.mul_dvd_mul h₁ h₂)
  have hle : d ≤ Nat.gcd n L*m :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ hn) hmpos) hdiv
  have hd' : (d:ℝ) ≤ (Nat.gcd n L:ℝ)*(m:ℝ) := by exact_mod_cast hle
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hm' : (q:ℝ)=(L:ℝ)*(m:ℝ) := by exact_mod_cast hm
  apply (div_le_div_iff₀ hq' hL').2
  calc
    _ ≤ ((Nat.gcd n L:ℝ)*(m:ℝ))*(L:ℝ) :=
      mul_le_mul_of_nonneg_right hd' hL'.le
    _ = _ := by rw [hm']; ring


end
end InnerFloorResearch

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open DyadicMixedB4CharacterFactorBound
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
variable {q : ℕ} [NeZero q]

def signedCoefficient (χ ψ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  canonicalPairCoefficient χ ψ (fun a => ZMod.stdAddChar (-(n:ZMod q)*(a:ZMod q)))

/-- Isolate the conductor factors of the two actual Fourier weights.
The third Gauss sum retains the signed information. -/
theorem signedCoefficient_norm_le (χ ψ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖signedCoefficient χ ψ n‖ ≤
      Real.sqrt χ.conductor * Real.sqrt ψ.conductor *
        ‖gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ /
          (q.totient:ℝ)^2 := by
  have h₁ := norm_dirichlet_gauss_standard χ⁻¹
  have h₂ := norm_dirichlet_gauss_standard ψ⁻¹
  rw [DirichletCharacter.conductor_inv] at h₁ h₂
  rw [signedCoefficient,signedPair_eq,norm_mul,norm_div,norm_mul,norm_pow,Complex.norm_natCast]
  calc
    _ ≤ (Real.sqrt χ.conductor * Real.sqrt ψ.conductor / (q.totient:ℝ)^2) *
        ‖gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul h₁ h₂ (norm_nonneg _) (Real.sqrt_nonneg _)) (sq_nonneg _))
        (norm_nonneg _)
    _ = _ := by ring

/-- Real high-product-conductor estimate with no coprimality restriction. -/
theorem signedCoefficient_highProduct (χ ψ : DirichletCharacter ℂ q)
    (n D : ℕ) (hn : 0 < n) (hDpos : 0 < D) (hD : D ≤ (χ*ψ).conductor) :
    ‖signedCoefficient χ ψ n‖ ≤ productCoefficient q χ.conductor ψ.conductor D := by
  apply (signedCoefficient_norm_le χ ψ n).trans
  unfold productCoefficient
  have hq : (1:ℝ)≤q := by exact_mod_cast NeZero.pos q
  have hlog : 0≤1+Real.log q := by linarith [Real.log_nonneg hq]
  have h := shiftedGauss_productConductor (χ*ψ) n hn
  have hden : 0 < Real.sqrt (D:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hDpos)
  have hshift : ‖gaussSum (χ*ψ) (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*(1+Real.log q)/Real.sqrt D :=
    h.trans (div_le_div_of_nonneg_left (by positivity) hden
      (Real.sqrt_le_sqrt (by exact_mod_cast hD)))
  calc
    _ ≤ Real.sqrt χ.conductor*Real.sqrt ψ.conductor*
        ((q:ℝ)*(1+Real.log q)/Real.sqrt D)/(q.totient:ℝ)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hshift (by positivity)) (sq_nonneg _)
    _ = _ := by ring

end
end InnerFloorGaussPacket

#print axioms InnerFloorGaussPacket.signedCoefficient_norm_le
#print axioms InnerFloorGaussPacket.signedCoefficient_highProduct

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open DyadicMixedB4CharacterFactorBound
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000

/-- Uniform product conductor under common lift. -/
theorem productConductor_changeLevel {L q : ℕ} [NeZero L] [NeZero q]
    (h : L∣q) (χ ψ : DirichletCharacter ℂ L) :
    (DirichletCharacter.changeLevel h χ * DirichletCharacter.changeLevel h ψ).conductor =
      (χ*ψ).conductor := by
  rw [← map_mul,DirichletCharacter.conductor_changeLevel]

/-- A finite common-multiple sum of the genuine signed coefficients times
continuous zero-pair integrals. Large product conductor gives a saving
even when the individual primitive levels are small. -/
theorem highProduct_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (β₁ γ₁ β₂ γ₂ : ℝ) (hβ₁ : 3/4≤β₁) (hβ₂ : 3/4≤β₂)
    (R : ℕ→ℝ) (hR : ∀ q∈S,0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * pairIntegral β₁ γ₁ β₂ γ₂ (R q)‖ ≤
      2*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  dsimp only
  let c (q : ℕ) := productCoefficient q χ.conductor ψ.conductor D
  have hc (q : ℕ) (hq : q∈S) :
      ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0)‖ ≤ c q := by
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    have hq0 : 0 < q := (mem_Icc.mp hqR).1
    rw [dif_pos ⟨hq0,hqL⟩]
    letI : NeZero q := ⟨hq0.ne'⟩
    have hp : D ≤ (DirichletCharacter.changeLevel hqL χ *
          DirichletCharacter.changeLevel hqL ψ).conductor := by
      rw [productConductor_changeLevel]
      exact hprod
    have h := signedCoefficient_highProduct
      (DirichletCharacter.changeLevel hqL χ) (DirichletCharacter.changeLevel hqL ψ) n D hn hD hp
    simpa only [c,DirichletCharacter.conductor_changeLevel] using h
  have hS' : S ⊆ (Icc 1 A).filter (fun q => χ.conductor∣q ∧ ψ.conductor∣q) := by
    intro q hq
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    exact mem_filter.mpr ⟨hqR,χ.conductor_dvd_level.trans hqL,ψ.conductor_dvd_level.trans hqL⟩
  have hsum : ∑ q∈S,c q ≤ weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
    apply (sum_le_sum_of_subset_of_nonneg hS' (fun q hq _ => ?_)).trans
      (productCoefficientFamily A χ.conductor ψ.conductor D
        (Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos L))
        (Nat.pos_of_dvd_of_pos ψ.conductor_dvd_level (NeZero.pos L)) hD)
    have hq0 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hq0
    have hlog := Real.log_nonneg hq1
    unfold productCoefficient
    positivity
  calc
    _ ≤ ∑ q∈S, ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0) *
        pairIntegral β₁ γ₁ β₂ γ₂ (R q)‖ := norm_sum_le _ _
    _ ≤ ∑ q∈S,c q*2 := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul (hc q hq) (pairIntegral_uniform β₁ γ₁ β₂ γ₂ (R q) hβ₁ hβ₂ (hR q hq))
        (norm_nonneg _) ((norm_nonneg _).trans (hc q hq))
    _ ≤ _ := by
      rw [← sum_mul]
      calc
        _ ≤ (weightConstant^3*(1+Real.log A)^4/Real.sqrt D)*2 :=
          mul_le_mul_of_nonneg_right hsum (by norm_num)
        _ = _ := by ring

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.productConductor_changeLevel
#print axioms InnerFloorGaussPacket.highProduct_sum

section
open Set MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform ContDiff BigOperators Interval
namespace InnerFloorZeroModel
noncomputable section
/-- Exactly the trapezoid used in the accepted canonical explicit formula. -/
def dyadicTaper (a b x : ℝ) : ℝ := max 0 (min (x-a) (min 1 (b+1-x)))

theorem dyadicTaper_bounds (a b x : ℝ) :
    0 ≤ dyadicTaper a b x ∧ dyadicTaper a b x ≤ 1 := by
  unfold dyadicTaper
  exact ⟨le_max_left _ _,max_le (by norm_num) ((min_le_right ..).trans (min_le_left ..))⟩

def dyadicKernel (a b : ℝ) (ρ : ℂ) : ℝ → ℂ :=
  (Ioc a (b+1)).indicator (fun x => (dyadicTaper a b x:ℂ)*(x:ℂ)^(ρ-1))

def dyadicTransform (a b : ℝ) (ρ : ℂ) (v : ℝ) : ℂ :=
  ∫ x in a..b+1, (dyadicTaper a b x:ℂ)*phase (2*Real.pi*v*x)*(x:ℂ)^(ρ-1)

theorem dyadicTransform_fourier (a b : ℝ) (ρ : ℂ) (v : ℝ)
    (hab : a ≤ b+1) :
    dyadicTransform a b ρ v = 𝓕 (dyadicKernel a b ρ) (-v) := by
  rw [Real.fourier_real_eq_integral_exp_smul,dyadicTransform,intervalIntegral.integral_of_le hab]
  have he : (fun x => Complex.exp (↑(-2*Real.pi*x*(-v))*Complex.I) • dyadicKernel a b ρ x) =
    (Ioc a (b+1)).indicator (fun x => (dyadicTaper a b x:ℂ)*phase (2*Real.pi*v*x)*(x:ℂ)^(ρ-1)) := by
    funext x
    by_cases hx : x∈Ioc a (b+1)
    · rw [dyadicKernel,Set.indicator_of_mem hx,Set.indicator_of_mem hx]
      simp only [smul_eq_mul,phase]
      rw [show (-2*Real.pi*x*(-v))=2*Real.pi*v*x by ring]
      ring
    · simp [dyadicKernel,Set.indicator_of_notMem hx]
  rw [he,integral_indicator measurableSet_Ioc]

theorem dyadicTransform_energy (a b N : ℝ) (ρ : ℂ)
    (ha : 0<a) (hab : a≤b+1) (hN : b+1≤N) (hρ : 1/2<ρ.re) :
    Integrable (fun v => ‖dyadicTransform a b ρ v‖^2) ∧
      (∫ v, ‖dyadicTransform a b ρ v‖^2) ≤ N^(2*ρ.re-1)/(2*ρ.re-1) := by
  let f (x : ℝ) : ℂ := (dyadicTaper a b x:ℂ)*(x:ℂ)^(ρ-1)
  have hcont : ContinuousOn f (Icc a (b+1)) := by
    intro x hx
    have hx0 : 0<x := ha.trans_le hx.1
    have ht : Continuous (fun x : ℝ => dyadicTaper a b x) := by unfold dyadicTaper;fun_prop
    exact ((Complex.continuous_ofReal.comp ht).continuousAt.mul
      (differentiableAt_id.ofReal_cpow_const (ρ-1) hx0.ne').continuousAt).continuousWithinAt
  have hf : IntegrableOn f (Ioc a (b+1)) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hfsq : IntegrableOn (fun x => ‖f x‖^2) (Ioc a (b+1)) :=
    (hcont.norm.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hki : Integrable (dyadicKernel a b ρ) := by
    rw [dyadicKernel,integrable_indicator_iff measurableSet_Ioc]
    exact hf
  have hksq : (fun x => ‖dyadicKernel a b ρ x‖^2) =
      (Ioc a (b+1)).indicator (fun x => ‖f x‖^2) := by
    funext x
    by_cases hx : x∈Ioc a (b+1) <;> simp [dyadicKernel,f,hx]
  have hk₂ : MemLp (dyadicKernel a b ρ) 2 :=
    (memLp_two_iff_integrable_sq_norm hki.aestronglyMeasurable).mpr (by
      rw [hksq,integrable_indicator_iff measurableSet_Ioc];exact hfsq)
  obtain ⟨hi,he⟩ := box_plancherel hki hk₂
  have hpow (x : ℝ) (hx : x∈Ioc a (b+1)) :
      ‖f x‖^2 ≤ x^(2*ρ.re-2) := by
    have hx0 : 0<x := ha.trans hx.1
    have ht := dyadicTaper_bounds a b x
    dsimp [f]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1,
      Complex.norm_cpow_eq_rpow_re_of_pos hx0,Complex.sub_re,Complex.one_re]
    calc
      _ ≤ (x^(ρ.re-1))^2 :=
        pow_le_pow_left₀ (mul_nonneg ht.1 (Real.rpow_nonneg hx0.le _))
          (mul_le_of_le_one_left (Real.rpow_nonneg hx0.le _) ht.2) 2
      _ = _ := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hx0.le]
        congr 1
        norm_num
        ring
  have hN0 : 0<N := ha.trans_le (hab.trans hN)
  have hp : IntegrableOn (fun x : ℝ => x^(2*ρ.re-2)) (Ioc 0 N) := by
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<2*ρ.re-2)).1
  have hsub : Ioc a (b+1) ⊆ Ioc 0 N :=
    fun x hx => ⟨ha.trans hx.1,hx.2.trans hN⟩
  have hfull : ∫ x, ‖dyadicKernel a b ρ x‖^2 ≤ N^(2*ρ.re-1)/(2*ρ.re-1) := by
    rw [hksq,integral_indicator measurableSet_Ioc]
    calc
      _ ≤ ∫ x in Ioc a (b+1), x^(2*ρ.re-2) :=
        setIntegral_mono_on hfsq (hp.mono_set hsub) measurableSet_Ioc hpow
      _ ≤ ∫ x in Ioc 0 N, x^(2*ρ.re-2) :=
        setIntegral_mono_set hp (by
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
          exact Real.rpow_nonneg hx.1.le _) (Filter.Eventually.of_forall hsub)
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hN0.le,
          integral_rpow (Or.inl (by linarith : -1<2*ρ.re-2)),
          show 2*ρ.re-2+1=2*ρ.re-1 by ring,Real.zero_rpow (by linarith : 2*ρ.re-1≠0),sub_zero]
  simp_rw [dyadicTransform_fourier a b ρ _ hab]
  constructor
  · simpa only [neg_one_mul] using hi.comp_mul_left' (by norm_num : (-1:ℝ)≠0)
  · calc
      _ = ∫ v, ‖𝓕 (dyadicKernel a b ρ) v‖^2 := by
        have h := Measure.integral_comp_mul_left (fun v => ‖𝓕 (dyadicKernel a b ρ) v‖^2) (-1:ℝ)
        simpa [neg_one_mul] using h
      _ ≤ _ := he.trans_le hfull


/-- The actual dyadic tapered pair with arbitrary windows.
This also permits the principal term rho=1. -/
def dyadicPair (a b c d : ℝ) (ρ σ : ℂ) (R n : ℝ) : ℂ :=
  ∫ v in -R..R, dyadicTransform a b ρ v * dyadicTransform c d σ v *
    phase (-(2*Real.pi*n*v))

theorem dyadicPair_uniform (a b c d N : ℝ) (ρ σ : ℂ) (R n : ℝ)
    (ha : 0<a) (hb : a≤b+1) (hc : 0<c) (hd : c≤d+1)
    (hbN : b+1≤N) (hdN : d+1≤N) (hN : 1≤N) (hR : 0≤R)
    (hρ : 3/4≤ρ.re) (hρ1 : ρ.re≤1)
    (hσ : 3/4≤σ.re) (hσ1 : σ.re≤1) :
    ‖dyadicPair a b c d ρ σ R n‖ ≤ 2*N := by
  obtain ⟨hi₁,he₁⟩ := dyadicTransform_energy a b N ρ ha hb hbN (by linarith)
  obtain ⟨hi₂,he₂⟩ := dyadicTransform_energy c d N σ hc hd hdN (by linarith)
  have hscalar (t : ℝ) (h₁ : 3/4≤t) (h₂ : t≤1) :
      N^(2*t-1)/(2*t-1)≤2*N := by
    have ht : 0<2*t-1 := by linarith
    have hp : N^(2*t-1)≤N := by
      calc
        _ ≤ N^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
        _ = _ := Real.rpow_one _
    apply (div_le_iff₀ ht).2
    have h := mul_le_mul_of_nonneg_left (show (1:ℝ)≤2*(2*t-1) by linarith) (by linarith : 0≤N)
    nlinarith only [hp,h]
  let f (v : ℝ) := (‖dyadicTransform a b ρ v‖^2+‖dyadicTransform c d σ v‖^2)/2
  have hf : Integrable f := (hi₁.add hi₂).div_const 2
  have hp (v : ℝ) :
      ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖≤f v := by
    rw [norm_mul,norm_mul,norm_phase,mul_one]
    dsimp [f]
    nlinarith [sq_nonneg (‖dyadicTransform a b ρ v‖-‖dyadicTransform c d σ v‖)]
  have hA : ∀ v,0≤f v := by intro v;dsimp [f];positivity
  unfold dyadicPair
  rw [intervalIntegral.integral_of_le (by linarith : -R≤R)]
  calc
    _ ≤ ∫ v in Ioc (-R) R, ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioc (-R) R,f v :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hf.integrableOn (Filter.Eventually.of_forall hp)
    _ ≤ ∫ v,f v := setIntegral_le_integral hf (Filter.Eventually.of_forall hA)
    _ ≤ 2*N := by
      dsimp [f]
      rw [integral_div,integral_add hi₁ hi₂]
      linarith only [he₁.trans (hscalar ρ.re hρ hρ1), he₂.trans (hscalar σ.re hσ hσ1)]


end
end InnerFloorZeroModel
end

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000
theorem boundedHighProduct_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 0≤N) (J : ℕ→ℂ) (hJ : ∀ q∈S, ‖J q‖≤2*N) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * J q‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  dsimp only
  let c (q : ℕ) := productCoefficient q χ.conductor ψ.conductor D
  have hc (q : ℕ) (hq : q∈S) :
      ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0)‖ ≤ c q := by
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    have hq0 : 0 < q := (mem_Icc.mp hqR).1
    rw [dif_pos ⟨hq0,hqL⟩]
    letI : NeZero q := ⟨hq0.ne'⟩
    have hp : D ≤ (DirichletCharacter.changeLevel hqL χ *
          DirichletCharacter.changeLevel hqL ψ).conductor := by
      rw [productConductor_changeLevel]
      exact hprod
    have h := signedCoefficient_highProduct
      (DirichletCharacter.changeLevel hqL χ) (DirichletCharacter.changeLevel hqL ψ) n D hn hD hp
    simpa only [c,DirichletCharacter.conductor_changeLevel] using h
  have hS' : S ⊆ (Icc 1 A).filter (fun q => χ.conductor∣q ∧ ψ.conductor∣q) := by
    intro q hq
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    exact mem_filter.mpr ⟨hqR,χ.conductor_dvd_level.trans hqL,ψ.conductor_dvd_level.trans hqL⟩
  have hsum : ∑ q∈S,c q ≤ weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
    apply (sum_le_sum_of_subset_of_nonneg hS' (fun q hq _ => ?_)).trans
      (productCoefficientFamily A χ.conductor ψ.conductor D
        (Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos L))
        (Nat.pos_of_dvd_of_pos ψ.conductor_dvd_level (NeZero.pos L)) hD)
    have hq0 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hq0
    have hlog := Real.log_nonneg hq1
    unfold productCoefficient
    positivity
  calc
    _ ≤ ∑ q∈S, ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0) *
        J q‖ := norm_sum_le _ _
    _ ≤ ∑ q∈S,c q*(2*N) := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul (hc q hq) (hJ q hq)
        (norm_nonneg _) ((norm_nonneg _).trans (hc q hq))
    _ ≤ _ := by
      rw [← sum_mul]
      calc
        _ ≤ (weightConstant^3*(1+Real.log A)^4/Real.sqrt D)*(2*N) :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
        _ = _ := by ring

/-- Exact taper-model version of the high-product packet estimate.
The radius and both dyadic windows may depend on the modulus. -/
theorem dyadicHighProduct_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hρ1 : ρ.re≤1) (hσ : 3/4≤σ.re) (hσ1 : σ.re≤1)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  apply boundedHighProduct_sum χ ψ A n D hn hD hprod S hS N (by linarith)
  intro q hq
  exact dyadicPair_uniform (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hρ1 hσ hσ1

end
end InnerFloorGaussPacket
#print axioms InnerFloorZeroModel.dyadicTransform_energy
#print axioms InnerFloorZeroModel.dyadicPair_uniform
#print axioms InnerFloorGaussPacket.boundedHighProduct_sum
#print axioms InnerFloorGaussPacket.dyadicHighProduct_sum

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open DyadicMixedB4CharacterFactorBound
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem shiftedGauss_commonRatio {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (n L : ℕ) (hn : 0 < n)
    (hL : 0 < L) (hLq : L∣q) :
    ‖gaussSum χ (ZMod.stdAddChar.mulShift (-(n:ZMod q)))‖ ≤
      (q:ℝ)*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))*(1+Real.log q) := by
  have hq : 0 < q := NeZero.pos q
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hlog : 0≤1+Real.log q := by linarith [Real.log_nonneg hq1]
  have hratio := gcdRatio_mono_multiple n L q hn hL hLq hq
  let r := (Nat.gcd n L:ℝ)/(L:ℝ)
  have hr : 0≤r := by dsimp [r]; positivity
  have hsq : (q:ℝ)*(Nat.gcd n q:ℝ) ≤ (q:ℝ)^2*r := by
    have h := (div_le_iff₀ hqR).mp hratio
    change (Nat.gcd n q:ℝ) ≤ r*(q:ℝ) at h
    calc
      _ ≤ (q:ℝ)*(r*(q:ℝ)) := mul_le_mul_of_nonneg_left h hqR.le
      _ = _ := by ring
  have hs : Real.sqrt ((q:ℝ)*(Nat.gcd n q:ℝ)) ≤ (q:ℝ)*Real.sqrt r := by
    calc
      _ ≤ Real.sqrt ((q:ℝ)^2*r) := Real.sqrt_le_sqrt hsq
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hqR.le]
  exact (shiftedGauss_geometricGcd χ n hn).trans (mul_le_mul_of_nonneg_right hs hlog)

/-- The common-level coefficient has a square-root saving when only a small
fraction of that level divides n. This applies to any product conductor. -/
theorem signedCoefficient_commonRatio {L q : ℕ} [NeZero L] [NeZero q]
    (hLq : L∣q) (χ ψ : DirichletCharacter ℂ L) (n A : ℕ)
    (hn : 0 < n) (hqA : q≤A) :
    ‖signedCoefficient (DirichletCharacter.changeLevel hLq χ)
      (DirichletCharacter.changeLevel hLq ψ) n‖ ≤
      weightConstant*(1+Real.log A)^2*
      Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))*((L:ℝ)/(q.totient:ℝ)) := by
  have hq : 0 < q := NeZero.pos q
  have hL : 0 < L := NeZero.pos L
  have hφ : (0:ℝ)<q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hlogq := Real.log_nonneg hq1
  have hlog : Real.log q≤Real.log A :=
    Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqA)
  have hlogA : 0≤Real.log A := hlogq.trans hlog
  have hratio : (q:ℝ)/(q.totient:ℝ)≤weightConstant*(1+Real.log A) :=
    (ratio_totient_le q hq).trans
      (mul_le_mul_of_nonneg_left (by linarith) weightConstant_nonneg)
  have hdχ : χ.conductor≤L := Nat.le_of_dvd hL χ.conductor_dvd_level
  have hdψ : ψ.conductor≤L := Nat.le_of_dvd hL ψ.conductor_dvd_level
  have hroot : Real.sqrt χ.conductor * Real.sqrt ψ.conductor ≤ (L:ℝ) := by
    calc
      _ ≤ Real.sqrt (L:ℝ)*Real.sqrt (L:ℝ) :=
        mul_le_mul (Real.sqrt_le_sqrt (by exact_mod_cast hdχ))
          (Real.sqrt_le_sqrt (by exact_mod_cast hdψ))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg _)
  let r := Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))
  have hr : 0≤r := Real.sqrt_nonneg _
  let C := DirichletCharacter.changeLevel hLq χ
  let P := DirichletCharacter.changeLevel hLq ψ
  have hb := signedCoefficient_norm_le C P n
  dsimp [C,P] at hb
  rw [DirichletCharacter.conductor_changeLevel,DirichletCharacter.conductor_changeLevel] at hb
  have hshift := shiftedGauss_commonRatio (C*P) n L hn hL hLq
  calc
    _ ≤ _ := hb
    _ ≤ (L:ℝ)*((q:ℝ)*r*(1+Real.log q))/(q.totient:ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hroot hshift (norm_nonneg _) (Nat.cast_nonneg _)
    _ = ((L:ℝ)/(q.totient:ℝ))*((q:ℝ)/(q.totient:ℝ))*(1+Real.log q)*r := by ring
    _ ≤ ((L:ℝ)/(q.totient:ℝ))*(weightConstant*(1+Real.log A))*(1+Real.log A)*r := by
      apply mul_le_mul_of_nonneg_right _ hr
      apply mul_le_mul _ (by linarith) (by linarith)
        (mul_nonneg (by positivity) (mul_nonneg weightConstant_nonneg (by linarith)))
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

theorem boundedGcdRatio_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n : ℕ) (hn : 0 < n) (hLA : L≤A)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 0≤N) (J : ℕ→ℂ) (hJ : ∀ q∈S, ‖J q‖≤2*N) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * J q‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ)) := by
  dsimp only
  let K := weightConstant*(1+Real.log A)^2*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ))
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg weightConstant_nonneg (sq_nonneg _)) (Real.sqrt_nonneg _)
  have hcoef (q : ℕ) (hq : q∈S) :
      ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0)‖ ≤ K*((L:ℝ)/(q.totient:ℝ)) := by
    obtain ⟨hqR,hqL⟩ := mem_filter.mp (hS hq)
    obtain ⟨hq0,hqA⟩ := mem_Icc.mp hqR
    rw [dif_pos ⟨hq0,hqL⟩]
    letI : NeZero q := ⟨(show 0 < q from hq0).ne'⟩
    exact signedCoefficient_commonRatio hqL χ ψ n A hn hqA
  have hsum : ∑ q∈S,(L:ℝ)/(q.totient:ℝ) ≤ (weightConstant*(1+Real.log A))^2 :=
    (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)).trans
      (commonMultipleTotientWeight A L (NeZero.pos L) hLA)
  calc
    _ ≤ ∑ q∈S, ‖(if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n else 0) *
        J q‖ := norm_sum_le _ _
    _ ≤ ∑ q∈S, (K*((L:ℝ)/(q.totient:ℝ)))*(2*N) := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul (hcoef q hq) (hJ q hq)
        (norm_nonneg _) ((norm_nonneg _).trans (hcoef q hq))
    _ = K*(∑ q∈S,(L:ℝ)/(q.totient:ℝ))*(2*N) := by rw [← sum_mul,← mul_sum]
    _ ≤ K*((weightConstant*(1+Real.log A))^2)*(2*N) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hK) (by positivity)
    _ = _ := by dsimp [K];ring

theorem dyadicGcdRatio_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n : ℕ) (hn : 0 < n) (hLA : L≤A)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hρ1 : ρ.re≤1) (hσ : 3/4≤σ.re) (hσ1 : σ.re≤1)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N*weightConstant^3*(1+Real.log A)^4*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ)) := by
  apply boundedGcdRatio_sum χ ψ A n hn hLA S hS N (by linarith)
  intro q hq
  exact dyadicPair_uniform (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hρ1 hσ hσ1

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.shiftedGauss_commonRatio
#print axioms InnerFloorGaussPacket.signedCoefficient_commonRatio
#print axioms InnerFloorGaussPacket.boundedGcdRatio_sum
#print axioms InnerFloorGaussPacket.dyadicGcdRatio_sum

section
open Set MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform ContDiff BigOperators Interval
namespace InnerFloorZeroModel
noncomputable section
set_option maxHeartbeats 2000000 in
/-- Preserve both zero real parts in the exact taper pair bound, rather than
discarding their combined power saving by replacing the energy by O(N). -/
theorem dyadicPair_realParts (a b c d N : ℝ) (ρ σ : ℂ) (R n : ℝ)
    (ha : 0<a) (hb : a≤b+1) (hc : 0<c) (hd : c≤d+1)
    (hbN : b+1≤N) (hdN : d+1≤N) (hN : 1≤N) (hR : 0≤R)
    (hρ : 3/4≤ρ.re) (hσ : 3/4≤σ.re) :
    ‖dyadicPair a b c d ρ σ R n‖ ≤ 2*N^(ρ.re+σ.re-1) := by
  obtain ⟨hi₁,he₁⟩ := dyadicTransform_energy a b N ρ ha hb hbN (by linarith)
  obtain ⟨hi₂,he₂⟩ := dyadicTransform_energy c d N σ hc hd hdN (by linarith)
  have hN0 : 0<N := by linarith
  let X := N^(ρ.re-1/2)
  let Y := N^(σ.re-1/2)
  have hX : 0<X := Real.rpow_pos_of_pos hN0 _
  have hY : 0<Y := Real.rpow_pos_of_pos hN0 _
  have hXeq : N^(2*ρ.re-1)=X^2 := by
    dsimp [X]
    rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
    congr 1
    norm_num
    ring
  have hYeq : N^(2*σ.re-1)=Y^2 := by
    dsimp [Y]
    rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
    congr 1
    norm_num
    ring
  have hE₁ : (∫ v, ‖dyadicTransform a b ρ v‖^2) ≤ 2*X^2 := by
    apply he₁.trans
    rw [hXeq]
    apply (div_le_iff₀ (by linarith : 0<2*ρ.re-1)).2
    nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ)≤2*(2*ρ.re-1) by linarith) (sq_nonneg X)]
  have hE₂ : (∫ v, ‖dyadicTransform c d σ v‖^2) ≤ 2*Y^2 := by
    apply he₂.trans
    rw [hYeq]
    apply (div_le_iff₀ (by linarith : 0<2*σ.re-1)).2
    nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ)≤2*(2*σ.re-1) by linarith) (sq_nonneg Y)]
  let f (v : ℝ) := (‖dyadicTransform a b ρ v‖^2/X^2+‖dyadicTransform c d σ v‖^2/Y^2)/2
  have hf : Integrable f := ((hi₁.div_const (X^2)).add (hi₂.div_const (Y^2))).div_const 2
  have hF₁ : (∫ v, ‖dyadicTransform a b ρ v‖^2/X^2) ≤ 2 := by
    rw [integral_div]
    exact (div_le_iff₀ (pow_pos hX 2)).2 hE₁
  have hF₂ : (∫ v, ‖dyadicTransform c d σ v‖^2/Y^2) ≤ 2 := by
    rw [integral_div]
    exact (div_le_iff₀ (pow_pos hY 2)).2 hE₂
  have hF : (∫ v,f v) ≤ 2 := by
    dsimp [f]
    rw [integral_div,integral_add (hi₁.div_const _) (hi₂.div_const _)]
    linarith
  have hp (v : ℝ) :
      ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖≤(X*Y)*f v := by
    rw [norm_mul,norm_mul,norm_phase,mul_one]
    have h : ‖dyadicTransform a b ρ v‖*‖dyadicTransform c d σ v‖/(X*Y)≤f v := by
      dsimp [f]
      rw [show ‖dyadicTransform a b ρ v‖*‖dyadicTransform c d σ v‖/(X*Y)=
        (‖dyadicTransform a b ρ v‖/X)*(‖dyadicTransform c d σ v‖/Y) by
        field_simp]
      simp only [← div_pow]
      nlinarith [sq_nonneg (‖dyadicTransform a b ρ v‖/X-‖dyadicTransform c d σ v‖/Y)]
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hX hY)).1 h
  have hA : ∀ v,0≤(X*Y)*f v := by intro v;dsimp [f];positivity
  have hg : Integrable (fun v => (X*Y)*f v) := hf.const_mul _
  unfold dyadicPair
  rw [intervalIntegral.integral_of_le (by linarith : -R≤R)]
  calc
    _ ≤ ∫ v in Ioc (-R) R, ‖dyadicTransform a b ρ v*dyadicTransform c d σ v*phase (-(2*Real.pi*n*v))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioc (-R) R,(X*Y)*f v :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        hg.integrableOn (Filter.Eventually.of_forall hp)
    _ ≤ ∫ v,(X*Y)*f v := setIntegral_le_integral hg (Filter.Eventually.of_forall hA)
    _ ≤ 2*(X*Y) := by
      rw [integral_const_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hF (mul_pos hX hY).le
    _ = _ := by
      have hXY : X*Y=N^(ρ.re+σ.re-1) := by
        dsimp [X,Y]
        rw [← Real.rpow_add hN0]
        congr 1
        ring
      rw [hXY]

end
end InnerFloorZeroModel
end
#print axioms InnerFloorZeroModel.dyadicPair_realParts

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open scoped Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem dyadicHighProduct_realParts_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n D : ℕ) (hn : 0 < n) (hD : 0 < D)
    (hprod : D≤(χ*ψ).conductor)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hσ : 3/4≤σ.re)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N^(ρ.re+σ.re-1)*weightConstant^3*(1+Real.log A)^4/Real.sqrt D := by
  apply boundedHighProduct_sum χ ψ A n D hn hD hprod S hS (N^(ρ.re+σ.re-1)) (Real.rpow_nonneg (by linarith) _)
  intro q hq
  exact dyadicPair_realParts (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hσ

theorem dyadicGcdRatio_realParts_sum {L : ℕ} [NeZero L]
    (χ ψ : DirichletCharacter ℂ L) (A n : ℕ) (hn : 0 < n) (hLA : L≤A)
    (S : Finset ℕ) (hS : S ⊆ (Icc 1 A).filter (fun q => L∣q))
    (N : ℝ) (hN : 1≤N) (ρ σ : ℂ)
    (hρ : 3/4≤ρ.re) (hσ : 3/4≤σ.re)
    (a b c d R : ℕ→ℝ)
    (ha : ∀ q∈S, 0 < a q) (hb : ∀ q∈S, a q≤b q+1)
    (hc : ∀ q∈S, 0 < c q) (hd : ∀ q∈S, c q≤d q+1)
    (hbN : ∀ q∈S, b q+1≤N) (hdN : ∀ q∈S, d q+1≤N)
    (hR : ∀ q∈S, 0≤R q) :
    let C (q : ℕ) : ℂ :=
      if h : 0 < q ∧ L ∣ q then
        letI : NeZero q := ⟨h.1.ne'⟩
        signedCoefficient (DirichletCharacter.changeLevel h.2 χ)
          (DirichletCharacter.changeLevel h.2 ψ) n
      else 0
    ‖∑ q∈S, C q * dyadicPair (a q) (b q) (c q) (d q) ρ σ (R q) n‖ ≤
      2*N^(ρ.re+σ.re-1)*weightConstant^3*(1+Real.log A)^4*Real.sqrt ((Nat.gcd n L:ℝ)/(L:ℝ)) := by
  apply boundedGcdRatio_sum χ ψ A n hn hLA S hS (N^(ρ.re+σ.re-1)) (Real.rpow_nonneg (by linarith) _)
  intro q hq
  exact dyadicPair_realParts (a q) (b q) (c q) (d q) N ρ σ (R q) n
    (ha q hq) (hb q hq) (hc q hq) (hd q hq) (hbN q hq) (hdN q hq)
    hN (hR q hq) hρ hσ

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.dyadicHighProduct_realParts_sum
#print axioms InnerFloorGaussPacket.dyadicGcdRatio_realParts_sum


open scoped BigOperators
namespace InnerFloorResearch
noncomputable section

/-- A signed packet family can be reduced to the exceptional intersection of
all failed gates, retaining exact residual signs rather than replacing those
terms by their absolute values. The budgets apply only to the packet model. -/
theorem signedResidualPartition {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) (P Q R : ι → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred R] (N L C r m : ℝ)
    (hN : 0 ≤ N) (hL : 0 < L) (hC : 0 ≤ C)
    (hcard : (s.card : ℝ) ≤ L^r)
    (hP : ∀ i ∈ s, P i → ‖z i‖ ≤ C*(N/L^(m+r)))
    (hQ : ∀ i ∈ s, Q i → ‖z i‖ ≤ C*(N/L^(m+r)))
    (hR : ∀ i ∈ s, R i → ‖z i‖ ≤ C*(N/L^(m+r))) :
    (∑ i ∈ s.filter (fun i => ¬P i ∧ ¬Q i ∧ ¬R i), (z i).re) - C*(N/L^m)
      ≤ ∑ i ∈ s, (z i).re := by
  classical
  let G := s.filter (fun i => P i ∨ Q i ∨ R i)
  let B := s.filter (fun i => ¬P i ∧ ¬Q i ∧ ¬R i)
  have hG : G ⊆ s := Finset.filter_subset _ _
  have hdisj : Disjoint G B := by
    apply Finset.disjoint_left.mpr
    intro i hiG hiB
    have hg := (Finset.mem_filter.mp hiG).2
    have hb := (Finset.mem_filter.mp hiB).2
    rcases hg with h | h | h
    · exact hb.1 h
    · exact hb.2.1 h
    · exact hb.2.2 h
  have hcover : G ∪ B = s := by
    ext i
    simp only [G,B,Finset.mem_union,Finset.mem_filter]
    tauto
  have hpos : 0 ≤ C*(N/L^(m+r)) := by positivity
  have hsum : ∑ i ∈ G, ‖z i‖ ≤ C*(N/L^m) := by
    calc
      ∑ i ∈ G, ‖z i‖ ≤ ∑ _i ∈ G, C*(N/L^(m+r)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hs := hG hi
        rcases (Finset.mem_filter.mp hi).2 with h | h | h
        · exact hP i hs h
        · exact hQ i hs h
        · exact hR i hs h
      _ = (G.card:ℝ)*(C*(N/L^(m+r))) := by simp
      _ ≤ L^r*(C*(N/L^(m+r))) := by
        apply mul_le_mul_of_nonneg_right _ hpos
        exact (show (G.card:ℝ) ≤ (s.card:ℝ) by exact_mod_cast Finset.card_le_card hG).trans hcard
      _ = C*(N/L^m) := by
        rw [Real.rpow_add hL]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hL m), ne_of_gt (Real.rpow_pos_of_pos hL r)]
  have hgood : -(C*(N/L^m)) ≤ ∑ i ∈ G, (z i).re := by
    have hn : -(∑ i ∈ G, ‖z i‖) ≤ ∑ i ∈ G, (z i).re := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have habs := Complex.abs_re_le_norm (z i)
      exact (neg_le_neg habs).trans (neg_abs_le _)
    linarith
  have hsplit : ∑ i ∈ s, (z i).re = (∑ i ∈ G, (z i).re) + (∑ i ∈ B, (z i).re) := by
    rw [← hcover, Finset.sum_union hdisj]
  change (∑ i ∈ B, (z i).re) - C*(N/L^m) ≤ _
  linarith

end
end InnerFloorResearch
#print axioms InnerFloorResearch.signedResidualPartition

open scoped BigOperators
namespace InnerFloorResearch
noncomputable section

/-- Exponential form of the quantitative zero-pair deficit, retaining the
    logarithmic loss of the sparse family. This is a conditional numerical
    estimate only, not a zero-free region. -/
theorem sparseDeficitTerm (N L b c k m : ℝ)
    (hN : 0 < N) (hL : 0 < L)
    (hgap : (k+m)*Real.log L ≤ (2-b-c)*Real.log N) :
    N^(b+c-1)*L^k ≤ N/L^m := by
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL m)).2
  rw [Real.rpow_def_of_pos hN, Real.rpow_def_of_pos hL,
    Real.rpow_def_of_pos hL, ← Real.exp_add, ← Real.exp_add]
  calc
    _ ≤ Real.exp (Real.log N) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hgap]
    _ = N := Real.exp_log hN

/-- A log-power-sized packet family is small when each pair has the required
    real-part deficit, without multiplying by the total number of moduli. -/
theorem sparseDeficitSum {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (N L C r k m : ℝ)
    (b c : ι → ℝ) (hN : 0 < N) (hL : 0 < L) (hC : 0 ≤ C)
    (hcard : (s.card : ℝ) ≤ L^r)
    (hw : ∀ i ∈ s, w i ≤ C * (N^(b i+c i-1)*L^k))
    (hgap : ∀ i ∈ s, (k+(m+r))*Real.log L ≤ (2-b i-c i)*Real.log N) :
    ∑ i ∈ s, w i ≤ C*(N/L^m) := by
  have hden : 0 < L^(m+r) := Real.rpow_pos_of_pos hL _
  have hq : 0 ≤ C*(N/L^(m+r)) := mul_nonneg hC (div_nonneg hN.le hden.le)
  calc
    ∑ i ∈ s, w i ≤ ∑ _i ∈ s, C*(N/L^(m+r)) :=
      Finset.sum_le_sum fun i hi => (hw i hi).trans
        (mul_le_mul_of_nonneg_left (sparseDeficitTerm N L (b i) (c i) k (m+r) hN hL (hgap i hi)) hC)
    _ = (s.card : ℝ)*(C*(N/L^(m+r))) := by simp
    _ ≤ L^r*(C*(N/L^(m+r))) := mul_le_mul_of_nonneg_right hcard hq
    _ = C*(N/L^m) := by
      rw [Real.rpow_add hL]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hL m), ne_of_gt (Real.rpow_pos_of_pos hL r)]

end
end InnerFloorResearch
#print axioms InnerFloorResearch.sparseDeficitTerm
#print axioms InnerFloorResearch.sparseDeficitSum

namespace InnerFloorResearch
noncomputable section
open scoped BigOperators

/-- Convert a saving factor to an inverse logarithmic budget. -/
theorem packetSavingBudget (N L C b c k m r g : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C) (hg : 0 ≤ g)
    (hb : b+c ≤ 2) (hgate : L^(k+(m+r))*g ≤ 1) :
    C*(N^(b+c-1)*L^k)*g ≤ C*(N/L^(m+r)) := by
  have hn : 0 < N := by linarith
  have hpow : N^(b+c-1) ≤ N := by
    conv_rhs => rw [← Real.rpow_one N]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hLr : 0 < L^(m+r) := Real.rpow_pos_of_pos hL _
  have hsmall : L^k*g ≤ 1/L^(m+r) := by
    apply (le_div_iff₀ hLr).2
    rw [Real.rpow_add hL] at hgate
    linarith only [show L^k*g*L^(m+r) = L^k*L^(m+r)*g by ring,hgate]
  calc
    _ = C*(N^(b+c-1)*(L^k*g)) := by ring
    _ ≤ C*(N*(1/L^(m+r))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact mul_le_mul hpow hsmall (by positivity) hn.le
    _ = _ := by ring

/-- All three quantitative mechanisms simultaneously.  The unsolved term is
exactly the intersection of their failure regions, not a signed estimate
for an unrelated union of arcs. -/
theorem quantitativeResidualPartition {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) (b c u v : ι → ℝ) (N L C k r m : ℝ)
    (hN : 1 ≤ N) (hL : 0 < L) (hC : 0 ≤ C)
    (hcard : (s.card:ℝ) ≤ L^r)
    (hb : ∀ i ∈ s, b i+c i ≤ 2)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (h0 : ∀ i ∈ s, ‖z i‖ ≤ C*(N^(b i+c i-1)*L^k))
    (h1 : ∀ i ∈ s, ‖z i‖ ≤ C*(N^(b i+c i-1)*L^k)*u i)
    (h2 : ∀ i ∈ s, ‖z i‖ ≤ C*(N^(b i+c i-1)*L^k)*v i) :
    (∑ i ∈ s.filter (fun i =>
      (2-b i-c i)*Real.log N < (k+(m+r))*Real.log L ∧
      1 < L^(k+(m+r))*u i ∧ 1 < L^(k+(m+r))*v i), (z i).re)
      - C*(N/L^m) ≤ ∑ i ∈ s, (z i).re := by
  classical
  let P (i : ι) := (k+(m+r))*Real.log L ≤ (2-b i-c i)*Real.log N
  let Q (i : ι) := L^(k+(m+r))*u i ≤ 1
  let R (i : ι) := L^(k+(m+r))*v i ≤ 1
  have hn : 0 < N := by linarith
  have hP : ∀ i ∈ s, P i → ‖z i‖ ≤ C*(N/L^(m+r)) := by
    intro i hi hp
    exact (h0 i hi).trans (mul_le_mul_of_nonneg_left
      (sparseDeficitTerm N L (b i) (c i) k (m+r) hn hL hp) hC)
  have hQ : ∀ i ∈ s, Q i → ‖z i‖ ≤ C*(N/L^(m+r)) := by
    intro i hi hq
    exact (h1 i hi).trans (packetSavingBudget N L C (b i) (c i) k m r (u i) hN hL hC (hu i hi) (hb i hi) hq)
  have hR : ∀ i ∈ s, R i → ‖z i‖ ≤ C*(N/L^(m+r)) := by
    intro i hi hr
    exact (h2 i hi).trans (packetSavingBudget N L C (b i) (c i) k m r (v i) hN hL hC (hv i hi) (hb i hi) hr)
  simpa only [P,Q,R,not_le] using signedResidualPartition s z P Q R N L C r m
    hn.le hL hC hcard hP hQ hR

end
end InnerFloorResearch
#print axioms InnerFloorResearch.packetSavingBudget
#print axioms InnerFloorResearch.quantitativeResidualPartition

namespace InnerFloorGaussPacket
open Finset InnerFloorLinearTotient InnerFloorResearch InnerFloorZeroModel
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

/-- Data for one primitive-zero pair, lifted to a common level. The windows
may vary with the rational denominator; the arc mask is kept as a subset. -/
structure DyadicPacket where
  level : ℕ
  level_pos : 0 < level
  χ : DirichletCharacter ℂ level
  ψ : DirichletCharacter ℂ level
  ρ : ℂ
  σ : ℂ
  S : Finset ℕ
  a : ℕ → ℝ
  b : ℕ → ℝ
  c : ℕ → ℝ
  d : ℕ → ℝ
  R : ℕ → ℝ

def DyadicPacket.value (p : DyadicPacket) (n : ℕ) : ℂ :=
  ∑ q∈p.S, (if h : 0 < q ∧ p.level ∣ q then
    letI : NeZero q := ⟨h.1.ne'⟩
    signedCoefficient (DirichletCharacter.changeLevel h.2 p.χ)
      (DirichletCharacter.changeLevel h.2 p.ψ) n else 0) *
    dyadicPair (p.a q) (p.b q) (p.c q) (p.d q) p.ρ p.σ (p.R q) n

def DyadicPacket.productSaving (p : DyadicPacket) : ℝ :=
  letI : NeZero p.level := ⟨p.level_pos.ne'⟩
  1 / Real.sqrt ((p.χ*p.ψ).conductor:ℝ)

def DyadicPacket.gcdSaving (p : DyadicPacket) (n : ℕ) : ℝ :=
  Real.sqrt ((Nat.gcd n p.level:ℝ)/(p.level:ℝ))

structure DyadicPacket.Admissible (p : DyadicPacket) (A : ℕ) (N : ℝ) : Prop where
  hLA : p.level ≤ A
  hS : p.S ⊆ (Icc 1 A).filter (fun q => p.level∣q)
  hρ : 3/4≤p.ρ.re
  hσ : 3/4≤p.σ.re
  hsum : p.ρ.re+p.σ.re≤2
  ha : ∀ q∈p.S, 0<p.a q
  hb : ∀ q∈p.S, p.a q≤p.b q+1
  hc : ∀ q∈p.S, 0<p.c q
  hd : ∀ q∈p.S, p.c q≤p.d q+1
  hbN : ∀ q∈p.S, p.b q+1≤N
  hdN : ∀ q∈p.S, p.d q+1≤N
  hR : ∀ q∈p.S, 0≤p.R q

/-- The same actual Gauss-normalized packet has all three bounds, with no
zero-free hypothesis, and no assertion about the prime spectral expansion. -/
theorem DyadicPacket.threeBounds (p : DyadicPacket) (A n : ℕ) (N : ℝ)
    (hn : 0<n) (hN : 1≤N) (hp : p.Admissible A N) :
    let B := (2*weightConstant^3)*(N^(p.ρ.re+p.σ.re-1)*(1+Real.log A)^(4:ℝ))
    ‖p.value n‖ ≤ B ∧ ‖p.value n‖ ≤ B*p.productSaving ∧
      ‖p.value n‖ ≤ B*p.gcdSaving n := by
  letI : NeZero p.level := ⟨p.level_pos.ne'⟩
  let D := (p.χ*p.ψ).conductor
  have hD : 0<D := Nat.pos_of_dvd_of_pos (p.χ*p.ψ).conductor_dvd_level p.level_pos
  have h0 := dyadicHighProduct_realParts_sum p.χ p.ψ A n 1 hn (by omega)
    (show 1≤D by omega) p.S hp.hS N hN p.ρ p.σ hp.hρ hp.hσ p.a p.b p.c p.d p.R
    hp.ha hp.hb hp.hc hp.hd hp.hbN hp.hdN hp.hR
  have h1 := dyadicHighProduct_realParts_sum p.χ p.ψ A n D hn hD le_rfl p.S hp.hS
    N hN p.ρ p.σ hp.hρ hp.hσ p.a p.b p.c p.d p.R
    hp.ha hp.hb hp.hc hp.hd hp.hbN hp.hdN hp.hR
  have h2 := dyadicGcdRatio_realParts_sum p.χ p.ψ A n hn hp.hLA p.S hp.hS
    N hN p.ρ p.σ hp.hρ hp.hσ p.a p.b p.c p.d p.R
    hp.ha hp.hb hp.hc hp.hd hp.hbN hp.hdN hp.hR
  dsimp only at h0 h1 h2 ⊢
  rw [show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast]
  constructor
  · change ‖p.value n‖ ≤ _
    apply (show ‖p.value n‖ ≤ _ from h0).trans_eq
    norm_num
    ring
  constructor
  · change ‖p.value n‖ ≤ _
    apply (show ‖p.value n‖ ≤ _ from h1).trans_eq
    unfold DyadicPacket.productSaving
    dsimp [D]
    ring
  · change ‖p.value n‖ ≤ _
    apply (show ‖p.value n‖ ≤ _ from h2).trans_eq
    unfold DyadicPacket.gcdSaving
    ring

/-- Exact three-gate residual bound for any sparse collection of actual
Gauss-normalized tapered zero pairs. Only the residual intersection needs a
signed lower bound, provided the spectral expansion and sparsity are proved. -/
theorem actualPacketResidual {ι : Type*} (s : Finset ι) (p : ι→DyadicPacket)
    (A n : ℕ) (N r m : ℝ) (hA : 1≤A) (hn : 0<n) (hN : 1≤N)
    (hp : ∀ i∈s, (p i).Admissible A N)
    (hcard : (s.card:ℝ) ≤ (1+Real.log A)^r) :
    let L := 1+Real.log A
    (∑ i∈s.filter (fun i =>
      (2-(p i).ρ.re-(p i).σ.re)*Real.log N < (4+(m+r))*Real.log L ∧
      1 < L^(4+(m+r))*(p i).productSaving ∧
      1 < L^(4+(m+r))*(p i).gcdSaving n), ((p i).value n).re)
      -(2*weightConstant^3)*(N/L^m) ≤ ∑ i∈s, ((p i).value n).re := by
  dsimp only
  have hlog : 0 < 1+Real.log A := by
    linarith [Real.log_nonneg (show (1:ℝ)≤A by exact_mod_cast hA)]
  apply quantitativeResidualPartition s (fun i => (p i).value n)
    (fun i => (p i).ρ.re) (fun i => (p i).σ.re)
    (fun i => (p i).productSaving) (fun i => (p i).gcdSaving n)
    N (1+Real.log A) (2*weightConstant^3) 4 r m hN hlog
    (mul_nonneg (by norm_num) (pow_nonneg weightConstant_nonneg 3)) hcard
  · intro i hi; exact (hp i hi).hsum
  · intro i hi; unfold DyadicPacket.productSaving; positivity
  · intro i hi; unfold DyadicPacket.gcdSaving; positivity
  · intro i hi; exact ((p i).threeBounds A n N hn hN (hp i hi)).1
  · intro i hi; exact ((p i).threeBounds A n N hn hN (hp i hi)).2.1
  · intro i hi; exact ((p i).threeBounds A n N hn hN (hp i hi)).2.2

end
end InnerFloorGaussPacket
#print axioms InnerFloorGaussPacket.DyadicPacket.threeBounds
#print axioms InnerFloorGaussPacket.actualPacketResidual
