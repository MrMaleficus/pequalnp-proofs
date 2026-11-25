import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8978

open PEqualNP.MetaComplexity

theorem ti_succ {m : ℕ} (x : Fin (m + 1) → Bool) :
    tableIndex x = (if x 0 = true then 1 else 0) + 2 * tableIndex (Fin.tail x) := by
  unfold tableIndex
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  have h2 : (∑ i : Fin m, if x i.succ = true then 2 ^ ((i.succ : Fin (m + 1)) : ℕ) else 0)
      = ∑ i : Fin m, 2 * (if Fin.tail x i = true then 2 ^ (i : ℕ) else 0) :=
    Finset.sum_congr rfl (fun i _ => by
      by_cases hx : x i.succ = true <;> simp [hx, Fin.tail, pow_succ, mul_comm])
  rw [h2]
  simp

theorem testBit_ti_full : ∀ (m : ℕ) (x : Fin m → Bool) (j : ℕ),
    (tableIndex x).testBit j = if h : j < m then x ⟨j, h⟩ else false := by
  intro m
  induction m with
  | zero =>
    intro x j
    simp [tableIndex]
  | succ m ih =>
    intro x j
    rw [ti_succ]
    cases j with
    | zero =>
      rw [dif_pos (by omega)]
      show _ = x 0
      cases hx : x 0 <;> simp [Nat.testBit_zero, Nat.add_mul_mod_self_left]
    | succ j =>
      rw [Nat.testBit_succ]
      have e : ((if x 0 = true then 1 else 0) + 2 * tableIndex (Fin.tail x)) / 2
          = tableIndex (Fin.tail x) := by
        split_ifs <;> omega
      rw [e, ih]
      by_cases hj : j < m
      · rw [dif_pos hj, dif_pos (by omega)]; rfl
      · rw [dif_neg hj, dif_neg (by omega)]

theorem main_aux : ∀ (k : ℕ) (u : Fin (2 ^ k)), PEqualNP.MetaComplexity.tableIndex (fun i : Fin k => (u : ℕ).testBit i) = (u : ℕ) := by
  intro k u
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_ti_full]
  by_cases hj : j < k
  · rw [dif_pos hj]
  · rw [dif_neg hj]
    symm
    apply Nat.testBit_eq_false_of_lt
    calc (u : ℕ) < 2 ^ k := u.isLt
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)

end PEqualNP.Outside.L_meta_8978

theorem PEqualNP.Outside.L_meta_8978 : ∀ (k : ℕ) (u : Fin (2 ^ k)), PEqualNP.MetaComplexity.tableIndex (fun i : Fin k => (u : ℕ).testBit i) = (u : ℕ) :=
  PEqualNP.Outside.L_meta_8978.main_aux
