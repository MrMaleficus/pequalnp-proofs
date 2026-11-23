import Mathlib

theorem PEqualNP.Outside.L_meta_293 : ∀ (m k : ℕ) (H : SimpleGraph (Fin m)) (Q : Fin m → Fin m → ℕ → Fin (m + 2 * k * (m * m)) → Prop), 1 ≤ k → (∀ (u v : Fin m) (p : ℕ) (x : Fin (m + 2 * k * (m * m))), Q u v p x ↔ (p = 0 ∧ x.val = u.val) ∨ (p = 2 * k + 1 ∧ x.val = v.val) ∨ (1 ≤ p ∧ p ≤ 2 * k ∧ x.val + 1 = m + 2 * k * (u.val * m + v.val) + p)) → ∃ S : SimpleGraph (Fin (m + 2 * k * (m * m))), (∀ x y : Fin (m + 2 * k * (m * m)), S.Adj x y ↔ ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧ ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))) := by
  intro m k H Q hk hQ
  let R : Fin (m + 2 * k * (m * m)) → Fin (m + 2 * k * (m * m)) → Prop := fun x y =>
    ∃ u v : Fin m, u < v ∧ H.Adj u v ∧ ∃ p : ℕ, p ≤ 2 * k ∧
      ((Q u v p x ∧ Q u v (p + 1) y) ∨ (Q u v p y ∧ Q u v (p + 1) x))
  refine ⟨⟨R, ?_, ?_⟩, fun x y => Iff.rfl⟩
  · constructor
    rintro x y ⟨u, v, huv, hadj, p, hp, h⟩
    exact ⟨u, v, huv, hadj, p, hp, h.symm⟩
  · constructor
    rintro x ⟨u, v, _, _, p, hp, h⟩
    have h' : Q u v p x ∧ Q u v (p + 1) x := by
      rcases h with h | h <;> exact h
    simp only [hQ] at h'
    have hu := u.isLt
    have hv := v.isLt
    omega
