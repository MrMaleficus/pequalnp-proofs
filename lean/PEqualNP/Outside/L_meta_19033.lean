import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19033

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem tpoly_le (p : Polynomial ℕ) (n : ℕ) (hn : 1 ≤ n) :
    p.eval n ≤ (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn hi')

theorem pbound (p : Polynomial ℕ) : ∃ c K', ∀ k, K' ≤ k → 2 * p.eval (2 * k) ≤ k ^ c := by
  obtain ⟨Cs, hCs⟩ : ∃ c, c = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = p.natDegree := ⟨_, rfl⟩
  refine ⟨d + 1, 2 * Cs * 2 ^ d + 1, ?_⟩
  intro k hk
  have h1 := tpoly_le p (2 * k) (by omega)
  rw [← hCs, ← hd] at h1
  have h2 : 2 * (Cs * (2 * k) ^ d) = (2 * Cs * 2 ^ d) * k ^ d := by rw [mul_pow]; ring
  have h3 : (2 * Cs * 2 ^ d) * k ^ d ≤ k * k ^ d := Nat.mul_le_mul_right _ (by omega)
  calc 2 * p.eval (2 * k) ≤ 2 * (Cs * (2 * k) ^ d) := Nat.mul_le_mul_left _ h1
    _ = (2 * Cs * 2 ^ d) * k ^ d := h2
    _ ≤ k * k ^ d := h3
    _ = k ^ (d + 1) := by rw [pow_succ, mul_comm]

theorem tadj_cast (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (y : List Bool) (m k : ℕ)
    (h : m = k) :
    PEqualNP.Represents.adjFun (k := m) (l := m) (A m) (fun i => y.getD i false) =
      PEqualNP.Represents.adjFun (k := k) (l := k) (A k) (fun i => y.getD i false) := by
  subst h; rfl

theorem tarith (k s c : ℕ) (hs : 2 * s ≤ k ^ c) :
    2 * s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) ≤
      4 * 2 ^ k + 2 * (k * 2 ^ ((k + 1) / 2)) + k ^ c := by
  generalize 2 ^ k = a at *
  generalize k * 2 ^ ((k + 1) / 2) = b at *
  generalize k ^ c = e at *
  omega

theorem main_aux : (∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (2 * s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2))) → ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool), (∀ c : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 * (k * 2 ^ ((k + 1) / 2)) + k ^ c)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  intro hconv A hA hL hsub
  obtain ⟨p, hp⟩ := hsub hL
  simp only [PEqualNP.CircuitLowerBounds.SIZE] at hp
  obtain ⟨c, K', hK'⟩ := pbound p
  obtain ⟨K, hK⟩ := hA c
  obtain ⟨k, hk⟩ : ∃ k, k = max K K' := ⟨_, rfl⟩
  apply hK k (by omega)
  obtain ⟨C, hCg, hCs, hCd⟩ := hp (2 * k)
  have hHC : HasCircuitSize (k + k) (PEqualNP.Represents.adjFun (A k))
      (p.eval (2 * k)) := by
    refine ⟨C, hCg, hCs, ?_⟩
    intro x
    have hlen : (List.ofFn x).length = 2 * k := by rw [List.length_ofFn]; ring
    have hd := hCd (List.ofFn x) hlen
    rw [Bool.eq_iff_iff, hd]
    have hfx : (fun i : Fin (k + k) => (List.ofFn x).getD i false) = x := by
      funext i; exact ofFn_getD x i i.isLt
    have key : PEqualNP.Represents.adjFun (k := (List.ofFn x).length / 2)
        (l := (List.ofFn x).length / 2) (A ((List.ofFn x).length / 2))
        (fun i => (List.ofFn x).getD i false) = PEqualNP.Represents.adjFun (A k) x := by
      rw [tadj_cast A (List.ofFn x) ((List.ofFn x).length / 2) k (by rw [hlen]; omega), hfx]
    constructor
    · intro h
      obtain ⟨_, h2⟩ := h
      exact key.symm.trans h2
    · intro h
      exact And.intro (by rw [hlen]; exact even_two_mul k) (key.trans h)
  obtain ⟨D, hD1, hD2, hD3⟩ := hconv k k _ (A k) hHC
  refine ⟨D, hD1, le_trans hD2 ?_, hD3⟩
  exact tarith k _ c (hK' k (by omega))

end PEqualNP.Outside.L_meta_19033

theorem PEqualNP.Outside.L_meta_19033 : (∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (2 * s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2))) → ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool), (∀ c : ℕ, ∃ K : ℕ, ∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 * (k * 2 ^ ((k + 1) / 2)) + k ^ c)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly :=
  PEqualNP.Outside.L_meta_19033.main_aux
