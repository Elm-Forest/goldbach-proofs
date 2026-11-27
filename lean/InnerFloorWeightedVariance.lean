import InnerFloorWindowScale

open Finset GBSkirtVariance
open GoldbachGRHWindow (primeLog)
open scoped Classical

namespace InnerFloorResearch

noncomputable section

/-- A clipped window contains at most `h / q + 2` members of one residue
class, including windows truncated at either end. -/
theorem cardWindowResidue {q : ℕ} [NeZero q] (n h m : ℕ) (r : ZMod q) :
    ((window n h m).filter (fun k : ℕ => (k : ZMod q) = r)).card ≤ h/q+2 := by
  let l := m+1-h
  let T := (window n h m).filter (fun k : ℕ => (k : ZMod q) = r)
  have hcard : T.card ≤ (Icc (l/q) ((l+h)/q)).card := by
    apply Finset.card_le_card_of_injOn (fun k : ℕ => k/q)
    · intro k hk
      have hk' := mem_Icc.mp (mem_filter.mp hk).1
      have hlo : l ≤ k := hk'.1
      have hhi : k ≤ l+h := by
        have hk'' := hk'.2.trans (min_le_left m n)
        dsimp [l]
        omega
      exact mem_Icc.mpr ⟨Nat.div_le_div_right hlo, Nat.div_le_div_right hhi⟩
    · intro k hk j hj he
      change k/q = j/q at he
      have hk' := (mem_filter.mp hk).2
      have hj' := (mem_filter.mp hj).2
      have hmod := (ZMod.natCast_eq_natCast_iff' k j q).mp (hk'.trans hj'.symm)
      calc
        k = k % q + q*(k/q) := (Nat.mod_add_div k q).symm
        _ = j % q + q*(j/q) := by rw [hmod, he]
        _ = j := Nat.mod_add_div j q
  apply hcard.trans
  rw [Nat.card_Icc]
  have hd := Nat.add_div_le_div_add_div_add_one l h q
  omega

theorem residueErrorWindowCap {q : ℕ} [NeZero q] (n h m : ℕ) (hn : 2 ≤ n)
    (r : ZMod q) :
    ‖residueError (window n h m) primeLog r‖ ≤
      ((h : ℝ)/q + 2)*Real.log (n : ℝ) + (h : ℝ)/q.totient := by
  let I := window n h m
  let J := I.filter (fun k : ℕ => (k : ZMod q) = r)
  have hL : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hcard₀ : (J.card : ℝ) ≤ ((h/q : ℕ) : ℝ)+2 := by
    exact_mod_cast (cardWindowResidue n h m r)
  have hq : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hd : ((h/q : ℕ) : ℝ) ≤ (h : ℝ)/q := by
    apply (le_div_iff₀ hq).2
    exact_mod_cast Nat.div_mul_le_self h q
  have hprime (k : ℕ) (hk : k ∈ J) : ‖primeLog k‖ ≤ Real.log (n : ℝ) := by
    have hkn : k ≤ n := ((mem_Icc.mp (mem_filter.mp hk).1).2.trans (min_le_right _ _))
    by_cases hp : k.Prime
    · simp only [primeLog, if_pos hp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le : (1 : ℝ) ≤ k))]
      exact Real.log_le_log (by exact_mod_cast hp.pos : 0 < (k : ℝ))
        (by exact_mod_cast hkn : (k : ℝ) ≤ n)
    · simpa [primeLog, hp] using hL
  have hsum : ‖∑ k ∈ J, primeLog k‖ ≤ ((h : ℝ)/q + 2)*Real.log (n : ℝ) := by
    calc
      _ ≤ ∑ k ∈ J, ‖primeLog k‖ := norm_sum_le J primeLog
      _ ≤ ∑ _k ∈ J, Real.log (n : ℝ) := sum_le_sum hprime
      _ = (J.card : ℝ)*Real.log (n : ℝ) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcard₀.trans (add_le_add_right hd 2)) hL
  have hmodel : ‖if IsUnit r then (I.card : ℂ)/(q.totient : ℂ) else 0‖ ≤
      (h : ℝ)/q.totient := by
    split_ifs
    · simpa only [norm_div, Complex.norm_natCast] using
        (div_le_div_of_nonneg_right (by exact_mod_cast card_window_le n h m : (I.card : ℝ) ≤ h)
          (Nat.cast_nonneg q.totient : (0 : ℝ) ≤ q.totient))
    · simpa using (div_nonneg (Nat.cast_nonneg h) (Nat.cast_nonneg q.totient) :
        0 ≤ (h : ℝ)/q.totient)
  change ‖(∑ k ∈ J, primeLog k) - (if IsUnit r then (I.card : ℂ)/(q.totient : ℂ) else 0)‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add hsum hmodel)

/-- In the reduced classes the Fourier weight is followed by a sum over
`φ(q)` residues. The nonunit contribution is bounded by `q (log q)^2`.
This is the per-window bound supplied by the size cap and the AP maximum. -/
theorem weightedWindowBound {q : ℕ} [NeZero q] (n h m : ℕ) (hn : 2 ≤ n) :
    (q : ℝ) * (∑ r : ZMod q, ‖residueError (window n h m) primeLog r‖^2) ≤
      (q : ℝ) * (((h : ℝ) + 2*q)*Real.log (n : ℝ) + h) *
          reducedMax (window n h m) q + (q : ℝ)*(Real.log (q : ℝ))^2 := by
  let I := window n h m
  let U := (univ : Finset (ZMod q)).filter IsUnit
  let V := (univ : Finset (ZMod q)).filter (fun r => ¬IsUnit r)
  let F (r : ZMod q) := ‖residueError I primeLog r‖
  let E := reducedMax I q
  let C := ((h : ℝ)/q + 2)*Real.log (n : ℝ) + (h : ℝ)/q.totient
  have hq : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hL : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hE : 0 ≤ E := reduced_nonneg I
  have hUcard : U.card = q.totient := by
    have he : U = (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
      ext r
      simp [U, IsUnit]
    rw [he, card_map, card_univ, ZMod.card_units_eq_totient]
  have hU : (∑ r ∈ U, F r ^ 2) ≤ (q.totient : ℝ)*C*E := by
    calc
      _ ≤ �� _r ∈ U, C*E := by
        apply sum_le_sum
        intro r hr
        rw [pow_two]
        exact mul_le_mul (residueErrorWindowCap n h m hn r)
          (reduced_le I r (mem_filter.mp hr).2) (norm_nonneg _) hC
      _ = _ := by simp [hUcard, mul_assoc]
  have hV : (∑ r ∈ V, F r) ≤ Real.log (q : ℝ) := by
    calc
      _ ≤ ∑ r ∈ V, ∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), ‖primeLog k‖ := by
        apply sum_le_sum
        intro r hr
        have hr' : ¬ IsUnit r := (mem_filter.mp hr).2
        change ‖(∑ k ∈ I.filter (fun k : ℕ => (k : ZMod q) = r), primeLog k) -
          (if IsUnit r then (I.card : ℂ)/(q.totient : ℂ) else 0)‖ ≤ _
        simpa only [if_neg hr', sub_zero] using
          norm_sum_le (I.filter (fun k : ℕ => (k : ZMod q) = r)) primeLog
      _ = ∑ k ∈ I.filter (fun k : ℕ => ¬ IsUnit (k : ZMod q)), ‖primeLog k‖ := by
        rw [Finset.sum_fiberwise_eq_sum_filter]
        simp [V]
      _ ≤ _ := GoldbachGRHWindow.primeLog_nonunit_mass_le I
  have hV₂ : (∑ r ∈ V, F r ^ 2) ≤ (Real.log (q : ℝ))^2 :=
    (Finset.sum_sq_le_sq_sum_of_nonneg (fun r (_ : r ∈ V) => norm_nonneg
      (residueError I primeLog r))).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hV 2)
  have hcap : (q.totient : ℝ)*C ≤ ((h : ℝ) + 2*q)*Real.log (n : ℝ) + h := by
    have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
    calc
      _ = (q.totient : ℝ)*(((h : ℝ)/q + 2)*Real.log (n : ℝ)) + h := by
        dsimp [C]
        rw [mul_add, mul_comm (q.totient : ℝ) ((h : ℝ)/q.totient),
          div_mul_cancel₀ _ hφ.ne']
      _ ≤ (q : ℝ)*(((h : ℝ)/q + 2)*Real.log (n : ℝ)) + h :=
        add_le_add_right (mul_le_mul_of_nonneg_right hφq (by positivity)) _
      _ = _ := by rw [← mul_assoc, mul_add, mul_comm (q : ℝ) ((h : ℝ)/q),
          div_mul_cancel₀ _ hq.ne']
  change (q : ℝ) * (∑ r : ZMod q, F r^2) ≤
    (q : ℝ)*(((h : ℝ)+2*q)*Real.log (n : ℝ)+h)*E + (q : ℝ)*(Real.log (q : ℝ))^2
  rw [← Finset.sum_filter_add_sum_filter_not (s := (univ : Finset (ZMod q))) (p := IsUnit)]
  change (q : ℝ)*((∑ r ∈ U, F r^2)+(∑ r ∈ V, F r^2)) ≤ _
  have h := mul_le_mul_of_nonneg_left
    (add_le_add (hU.trans (mul_le_mul_of_nonneg_right hcap hE)) hV₂) hq.le
  simpa only [mul_add, mul_assoc] using h

theorem variance_of_weighted_L1 (n Q A h : ℕ) (hn : 2 ≤ n) (hAn : A ≤ n) :
    (∑ q ∈ Ioc Q A, mass q n h) ≤
      (((h : ℝ)+2*A)*Real.log (n : ℝ)+h) *
        (∑ q ∈ Ioc Q A, (q : ℝ)*endpointSum q n h) +
      (A : ℝ)^2*((n+1+h : ℕ) : ℝ)*(Real.log (n : ℝ))^2 := by
  let S := Ioc Q A
  let L := Real.log (n : ℝ)
  let C := ((h : ℝ)+2*A)*L+h
  let M := ((n+1+h : ℕ) : ℝ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hterm (q : ℕ) (hq : q ∈ S) :
      mass q n h ≤ C*((q : ℝ)*endpointSum q n h) + (A : ℝ)*M*L^2 := by
    obtain ⟨hqQ,hqA⟩ := mem_Ioc.mp hq
    have hq₀ : 0 < q := by omega
    letI : NeZero q := ⟨hq₀.ne'⟩
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq₀
    have hqA' : (q : ℝ) ≤ A := by exact_mod_cast hqA
    have hlog₀ : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq₀)
    have hlog : Real.log (q : ℝ) ≤ L :=
      Real.log_le_log hqR (by exact_mod_cast hqA.trans hAn)
    let E (m : ℕ) := reducedMax (window n h m) q
    have hs := sum_le_sum (s := range (n+1+h)) (fun m _ =>
      weightedWindowBound (q := q) n h m hn)
    rw [mass, dite_eq_right hq₀.ne', endpointSum, dite_eq_right hq₀.ne', windowEnergy]
    change _ ≤ C*((q : ℝ)*(∑ m ∈ range (n+1+h), E m)) + (A : ℝ)*M*L^2
    calc
      _ ≤ (q : ℝ)*(((h : ℝ)+2*q)*L+h)*(∑ m ∈ range (n+1+h), E m) +
          M*((q : ℝ)*(Real.log (q : ℝ))^2) := by
        rw [Finset.mul_sum]
        convert hs using 1
        simp [E, L, M, sum_add_distrib, Finset.mul_sum]
      _ = (((h : ℝ)+2*q)*L+h)*((q : ℝ)*(∑ m ∈ range (n+1+h), E m)) +
          (q : ℝ)*M*(Real.log (q : ℝ))^2 := by ring
      _ ≤ _ := by
        have hE : 0 ≤ ∑ m ∈ range (n+1+h), E m := sum_nonneg fun _ _ => reduced_nonneg _
        dsimp only [C]
        gcongr
  change (∑ q ∈ S, mass q n h) ≤
    C*(∑ q ∈ S, (q : ℝ)*endpointSum q n h) + (A : ℝ)^2*M*L^2
  calc
    _ ≤ ∑ q ∈ S, (C*((q : ℝ)*endpointSum q n h) + (A : ℝ)*M*L^2) :=
      sum_le_sum hterm
    _ = C*(∑ q ∈ S, (q : ℝ)*endpointSum q n h) + (S.card : ℝ)*((A : ℝ)*M*L^2) := by
      rw [sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ _ := by
      have hcard : S.card ≤ A := by
        dsimp [S]
        rw [Nat.card_Ioc]
        exact Nat.sub_le _ _
      apply add_le_add_left
      calc
        _ ≤ (A : ℝ)*((A : ℝ)*M*L^2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
        _ = _ := by ring

/-- The finite-array implication with a modulus-independent coefficient is
false. This example concerns the size cap and maximum alone. -/
theorem noUniformCapToWeightedEnergy : ¬ ∃ C : ℝ, ∀ q : ℕ, 0 < q →
    ∀ (h E : ℝ) (f : Fin q → ℝ), 0 ≤ E → (∀ r, |f r| ≤ E ∧ |f r| ≤ h/q) →
    (q : ℝ)*(∑ r, (f r)^2) ≤ C*h*E := by
  rintro ⟨C, hC⟩
  obtain ⟨q, hq⟩ := exists_nat_gt (max C 0)
  have hq₀ : (0 : ℝ) < q := (le_max_right C 0).trans_lt hq
  have hqC : C < (q : ℝ) := (le_max_left C 0).trans_lt hq
  have h := hC q (by exact_mod_cast hq₀) (q : ℝ) 1 (fun _ => 1) zero_le_one
    (fun _ => by simp [hq₀.ne'])
  simp only [one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  nlinarith only [h, mul_pos hq₀ (sub_pos.mpr hqC)]

end
end InnerFloorResearch
