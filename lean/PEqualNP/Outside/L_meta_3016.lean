import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3016

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (T T' : Finset (Fin n)), ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1 → G.edgeFinset.card + T.card ≤ C.size + 1 := by
  intro n G _ C T T' h1 h2
  have h3 := Finset.card_le_card_sdiff_add_card (s := G.edgeFinset)
    (t := (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C))
  omega

end PEqualNP.Outside.L_meta_3016

theorem PEqualNP.Outside.L_meta_3016 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (T T' : Finset (Fin n)), ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1 → G.edgeFinset.card + T.card ≤ C.size + 1 :=
  PEqualNP.Outside.L_meta_3016.main_aux
