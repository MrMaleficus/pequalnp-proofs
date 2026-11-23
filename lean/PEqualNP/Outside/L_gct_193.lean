import Mathlib

/-- The circulant matrix with first row `(1, i, -i, -1)`. -/
noncomputable def L_gct_193_M : Fin 4 → Fin 4 → ℂ :=
  ![![1, Complex.I, -Complex.I, -1],
    ![-1, 1, Complex.I, -Complex.I],
    ![-Complex.I, -1, 1, Complex.I],
    ![Complex.I, -Complex.I, -1, 1]]

theorem L_gct_193_entry (i j : Fin 4) :
    (if j.val = i.val then (1 : ℂ) else if j.val = (i.val + 1) % 4 then Complex.I
      else if j.val = (i.val + 2) % 4 then -Complex.I else -1) = L_gct_193_M i j := by
  fin_cases i <;> fin_cases j <;> simp [L_gct_193_M]

/-- A permutation of `Fin 4` given by its values and those of its inverse. -/
def L_gct_193_P (v w : Fin 4 → Fin 4) (h₁ : Function.LeftInverse w v)
    (h₂ : Function.RightInverse w v) : Equiv.Perm (Fin 4) :=
  ⟨v, w, h₁, h₂⟩

/-- All 24 permutations of `Fin 4`. -/
def L_gct_193_L : List (Equiv.Perm (Fin 4)) := [
  L_gct_193_P ![0,1,2,3] ![0,1,2,3] (by decide) (by decide),
  L_gct_193_P ![0,1,3,2] ![0,1,3,2] (by decide) (by decide),
  L_gct_193_P ![0,2,1,3] ![0,2,1,3] (by decide) (by decide),
  L_gct_193_P ![0,2,3,1] ![0,3,1,2] (by decide) (by decide),
  L_gct_193_P ![0,3,1,2] ![0,2,3,1] (by decide) (by decide),
  L_gct_193_P ![0,3,2,1] ![0,3,2,1] (by decide) (by decide),
  L_gct_193_P ![1,0,2,3] ![1,0,2,3] (by decide) (by decide),
  L_gct_193_P ![1,0,3,2] ![1,0,3,2] (by decide) (by decide),
  L_gct_193_P ![1,2,0,3] ![2,0,1,3] (by decide) (by decide),
  L_gct_193_P ![1,2,3,0] ![3,0,1,2] (by decide) (by decide),
  L_gct_193_P ![1,3,0,2] ![2,0,3,1] (by decide) (by decide),
  L_gct_193_P ![1,3,2,0] ![3,0,2,1] (by decide) (by decide),
  L_gct_193_P ![2,0,1,3] ![1,2,0,3] (by decide) (by decide),
  L_gct_193_P ![2,0,3,1] ![1,3,0,2] (by decide) (by decide),
  L_gct_193_P ![2,1,0,3] ![2,1,0,3] (by decide) (by decide),
  L_gct_193_P ![2,1,3,0] ![3,1,0,2] (by decide) (by decide),
  L_gct_193_P ![2,3,0,1] ![2,3,0,1] (by decide) (by decide),
  L_gct_193_P ![2,3,1,0] ![3,2,0,1] (by decide) (by decide),
  L_gct_193_P ![3,0,1,2] ![1,2,3,0] (by decide) (by decide),
  L_gct_193_P ![3,0,2,1] ![1,3,2,0] (by decide) (by decide),
  L_gct_193_P ![3,1,0,2] ![2,1,3,0] (by decide) (by decide),
  L_gct_193_P ![3,1,2,0] ![3,1,2,0] (by decide) (by decide),
  L_gct_193_P ![3,2,0,1] ![2,3,1,0] (by decide) (by decide),
  L_gct_193_P ![3,2,1,0] ![3,2,1,0] (by decide) (by decide)]

theorem L_gct_193_nodup : L_gct_193_L.Nodup := by decide

theorem L_gct_193_univ : L_gct_193_L.toFinset = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [List.toFinset_card_of_nodup L_gct_193_nodup, Fintype.card_perm, Fintype.card_fin]
  rfl

set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.L_gct_193 : ∀ c : ℂ, (∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4, (1 + c * (if (σ i).val = i.val then (1 : ℂ) else if (σ i).val = (i.val + 1) % 4 then Complex.I else if (σ i).val = (i.val + 2) % 4 then -Complex.I else -1))) = 24 := by
  intro c
  simp only [L_gct_193_entry]
  rw [← L_gct_193_univ, List.sum_toFinset _ L_gct_193_nodup]
  simp [L_gct_193_L, L_gct_193_P, L_gct_193_M, Fin.prod_univ_four]
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have h3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, h2]; ring
  have h4 : Complex.I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]; norm_num
  ring_nf
  simp only [h2, h3, h4]
  ring_nf
