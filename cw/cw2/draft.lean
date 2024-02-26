/- ### Hello Steve -/

import Mathlib.Tactic


variable (G H : Type)[Group G][MulAction G X] (x : X)
variable(H : Subgroup G)
variable {g : G}



open QuotientGroup MulAction

def φ (g : G ⧸ MulAction.stabilizer G x) : X :=
Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]


theorem ofQuotientStabilizer_mem_orbit (g) : φ G x g ∈ orbit G x :=
  Quotient.inductionOn' g fun g => ⟨g, rfl⟩



theorem injective_φ : Function.Injective (φ G x) := by sorry

theorem surjective_φ : Function.Surjective (φ G x) := by sorry

/-# Final Theorem-/
theorem orbit_stab : (|X| = ∑ G.orbit(x.i)) (|X|= ∑[G : x.i.stab]) := by sorry
