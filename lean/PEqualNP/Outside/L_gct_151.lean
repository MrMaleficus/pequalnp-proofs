import Mathlib

theorem PEqualNP.Outside.L_gct_151 : ∀ (q : ℕ) (Z : Submodule ℂ (Fin q → ℂ)) (y : Fin q → ℂ), y ∈ Z → (Finset.univ.sum fun j : Fin q => y j) ≠ 0 → (∀ y' ∈ Z, (Finset.univ.sum fun j : Fin q => y' j) ≠ 0 → (∀ j : Fin q, y j = 0 → y' j = 0) → ∀ j : Fin q, y' j = 0 → y j = 0) → ∀ x ∈ Z, (∀ j : Fin q, y j = 0 → x j = 0) → ∃ c : ℂ, x = c • y := by
  intro q Z y hyZ hsum hmin x hxZ hxsupp
  -- `y` is not zero, so some coordinate `j` of it is nonzero.
  obtain ⟨j, hj⟩ : ∃ j : Fin q, y j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hsum (Finset.sum_eq_zero fun i _ => h i)
  refine ⟨x j / y j, ?_⟩
  set c : ℂ := x j / y j with hc
  set z : Fin q → ℂ := x - c • y with hz
  have hzZ : z ∈ Z := Z.sub_mem hxZ (Z.smul_mem c hyZ)
  have hzj : z j = 0 := by
    simp only [hz, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc]
    field_simp
    ring
  have hzsupp : ∀ i : Fin q, y i = 0 → z i = 0 := by
    intro i hi
    simp [hz, hi, hxsupp i hi]
  suffices hz0 : z = 0 by
    have := sub_eq_zero.mp hz0
    exact this
  by_contra hne
  obtain ⟨k, hk⟩ : ∃ k : Fin q, z k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  by_cases hzs : (Finset.univ.sum fun i : Fin q => z i) = 0
  · -- `y + t • z` keeps the sum of `y` and vanishes at `k`.
    set t : ℂ := -(y k / z k) with ht
    have hwZ : y + t • z ∈ Z := Z.add_mem hyZ (Z.smul_mem t hzZ)
    have hwsum : (Finset.univ.sum fun i : Fin q => (y + t • z) i) ≠ 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hzs, mul_zero, add_zero]
      exact hsum
    have hwsupp : ∀ i : Fin q, y i = 0 → (y + t • z) i = 0 := by
      intro i hi
      simp [hi, hzsupp i hi]
    have hwk : (y + t • z) k = 0 := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ht]
      field_simp
      ring
    have hyk : y k = 0 := hmin _ hwZ hwsum hwsupp k hwk
    exact hk (hzsupp k hyk)
  · exact hj (hmin z hzZ hzs hzsupp j hzj)
