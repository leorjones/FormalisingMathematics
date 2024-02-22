import Mathlib.Tactic


---Our basic variables/notation---
variable (G H: Type)[Group G][Group H]
variable {G H}
variable (φ : G →* H)

/- ## First Isomorphism Theorem (Attempt)-/

/- # Ker(φ) is Normal in G -/

---this lemma helps us simplify later
lemma mem_ker (φ: G →* H): x ∈ φ.ker ↔ φ x = 1 := by rfl


---proof mainly follows from using properties of homomorphisms and definition of normal subgroup
---have tactic could have been used in lieu of our mem_ker lemma
theorem normal_kernel (φ : G →* H) : Subgroup.Normal φ.ker := by
  constructor
  intros p q r
  have h1 : φ (r * p * r⁻¹) = φ r * φ p * φ r⁻¹ := by repeat rw [φ.map_mul]
  rw [mem_ker] at q
  rw [q, mul_one, map_mul_eq_one φ] at h1
  exact h1
  apply mul_inv_self



---G/Ker(φ) being a subgroup follows (generally for all quotients) from commutator
example (N : Subgroup G)[Subgroup.Normal N] : Subgroup (G⧸N) := by
 exact commutator (G ⧸ N)


/- # Using Lift to get G/Ker(φ) →* H -/

---First attempt : couldn't figure out equiv relation ≈ on group elements

lemma equiv (a b : G) (φ : G →* H): (a ≈ b → φ a = φ b) := by sorry

/--"Lifting" φ : G →* H to φ' : G/Ker(φ) →* H (BROKEN)-/
def qlift [Group G] [Group H] {N : Subgroup G} [Subgroup.Normal N]
(φ: G →* H) (_ : ∀ n ∈ N, n ∈  φ.ker) (q : G ⧸ N) : H :=  Quotient.lift φ equiv q


---Second attempt : using lift specific to QuotientGroup
---this requires our quotient  N to be within the kernel, which we prove trivially with ≤ and rfl

/--Lifting" φ : G →* H to φ' : G/Ker(φ) →* H-/
def qlift2  [Group G] [Group H] (φ: G →* H) : G⧸φ.ker →* H :=
---have h1 : N ≤ f.ker := Eq.le h  ** use this if you want to pass in your equivalece condition
  QuotientGroup.lift φ.ker φ (Eq.le rfl)



/- # Trying to get G →* Im(φ)-/

/--Converting φ : G →* H to φ': G →* Im(φ) (BROKEN)-/
def rlift (φ : G →* H)(a : G) : φ.range := by
  exact Set.rangeFactorization (fun y => φ y) a

/--Converting φ : G →* H to φ': G →* Im(φ) (BROKEN)-/
def rlift2 (φ : G →* H) : G →* φ.range := by
  exact MonoidHom.rangeRestrict φ

/--Converting φ : G →* H to φ': G →* Im(φ) (UNPROVED)-/
def rlift3 (φ : G →* H)(φ': G⧸φ.ker →* H) : G⧸φ.ker →* φ.range :=  by
  sorry


/- # Defining required Isomorphism -/

/--Defining isomorphism G⧸φ.ker ≃* φ.range-/
def first_iso_thm (φ: G →* H) :  G⧸φ.ker ≃* φ.range := {
  toFun := rlift3 φ (qlift2 φ)
  invFun := sorry --- λb ↦ axiom of choice?
  left_inv := sorry --- invFun toFun
  right_inv := sorry
  map_mul' := sorry}

#lint
