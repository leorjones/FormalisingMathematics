import Mathlib.Tactic

/- Introduces inductive type MyD₃ and its constructors. It is to become the Dihedral Group of the 3-gon (Triangle)
with the r i corresponding to rotations by 0, 120 and 240 degrees and the sr i corresponding to its
3 reflective symmetries -/
inductive MyD₃
  | r : ZMod 3 → MyD₃
  | sr: ZMod 3 → MyD₃
deriving DecidableEq, Fintype

namespace MyD₃

/- Defines the multiplication (Group Law) of elements of D₃. The indices i and j take values
of 0,1 and 2-/
def mul : MyD₃ → MyD₃ → MyD₃
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

/- Defines the multiplicative identity of MyD₃ as r 0-/
def one : MyD₃ := r 0

/- Map which generates the multiplicative inverse of any element of MyD₃ -/
def inv : MyD₃ → MyD₃
  | r i => r (-i)
  | sr i => sr i

/- Proof that the multiplication defined is associative -/
lemma D₃_assoc (a b c : MyD₃) : mul (mul a  b)  c =  mul a  (mul b  c) := by
cases' a with a1 a2
cases' b with b1 b2
cases' c with c1 c2
simp [mul]
ring
simp [mul]
ring
cases' c with c1 c2
simp [mul]
ring
simp [mul]
ring
cases' b with b1 b2
cases' c with c1 c2
simp [mul]
ring
simp [mul]
ring
cases' c with c1 c2
simp [mul]
ring
simp [mul]
ring

/- Left multiplication by the identity leaves any element unchanged -/
lemma D₃_one_mul (g : MyD₃): mul one g = g := by
cases' g with g1 g2
· simp [one, mul]
· simp [one, mul]

/- Right multiplication by the identity leaves any element unchanged -/
lemma D₃_mul_one (g : MyD₃): mul g one  = g := by
cases' g with g1 g2
· simp [one, mul]
· simp [one, mul]

/- Multiplication by the inverse returns the identity function -/
lemma D₃_mul_left_inv (g : MyD₃) : mul (inv g) g = one := by
cases' g with g1 g2
· simp [inv, mul, one]
· simp [inv, mul, one]

/- Verification that MyD₃ and the multiplication defined satisfy the criteria to be a group-/
instance : Group MyD₃ where
  mul := mul
  mul_assoc := by exact D₃_assoc
  one := one
  one_mul := by exact D₃_one_mul
  mul_one := by exact D₃_mul_one
  inv := inv
  mul_left_inv := by exact D₃_mul_left_inv

/- The order of MyD₃ is 6 -/
lemma My_D₃_card : Fintype.card MyD₃ = 6 := by rfl

end MyD₃

variable (n : ℕ)

/- Constructs a set of natural numbers containing n distinct elements: 0 to n-1 -/
def n_set : Set ℕ := Finset.range n

variable (a1 a2 a3 b1 b2 b3 c1 : n_set n)

/- Constructs a  new type, objects of this type are ordered lists of length 7, their entries taken from set (n_set n) -/
def n7 := n_set (n) × n_set (n) × n_set (n) × n_set (n) ×  n_set (n) × n_set (n) × n_set (n)

/- Demonstration of a different approach which avoids some difficulties caused by (n7 n) being a type not a set -/
#check Set.pi (@Finset.univ (Fin 7) _).toSet (fun _ => n_set n)

/- Visual example of an object of type (n7 n) -/
def example_element : n7 n := (a1, a2, a3, b1, b2, b3, c1)

/- Functions which permute the entries of an element of (n7 n). The elements of (n7 n) have been designed as abstractions of a problem involving
colourings of a triangular pattern, these functions correspond to rotations and refelections of these colourings -/
def rotation_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a3, a1, b2, b3, b1, c1)

def reflection_0_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a1, a3, a2, b3, b2, b1, c1)

def reflection_1_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a1, a3, b1, b3, b2, c1)

def reflection_2_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a3, a2, a1, b2, b1, b3, c1)

open MyD₃

/- Defines the group action of elements of MyD₃ on 'set' (n7 n) -/
def transform_action : MyD₃ → n7 n → n7 n
| r 0 => id
| r 1 => rotation_funct n
| r 2 => (rotation_funct n) ∘ (rotation_funct n)
| sr 0 => reflection_0_funct n
| sr 1 => reflection_1_funct n
| sr 2 => reflection_2_funct n

/- r 0 acts on elements of (n7 n) by leaving them unchanged -/
lemma identity_action (x : n7 n) : (transform_action n) (r 0) x = x := by exact rfl

/- Associativity of the group action. Left sorried as would be repetitive proof considering cases, as seen previously -/
lemma assoc_action (g₁ g₂ : MyD₃)(x : n7 n) :
(transform_action n) (g₁ * g₂) x = (transform_action n g₁) (transform_action n g₂ x) := by
sorry

/- Verification that transform_action satisfies the criteria to be a valid group action of MyD₃ on (n7 n) -/
instance : MulAction MyD₃ (n7 n) where
  smul := transform_action n
  one_smul := identity_action n
  mul_smul := assoc_action n

/- g • x is equal to transform_action applied to an element of D₃ and  (n7 n) -/
theorem trans_action_def (g : MyD₃)(x : n7 n) : g • x = transform_action n g x := by rfl

/- Defining shorter notation for convenience -/
local notation "Ψ" => Quotient <| orbitRel MyD₃ (n7 n)

/- Casting variables as Fintypes as project focused on finite groups and finite sets -/
variable (x : n7 n)
variable [Fintype (MyD₃ ⧸ stabilizer MyD₃ x)][∀ x : (n7 n), Fintype <| stabilizer MyD₃ x][∀ x : (n7 n), Fintype (orbit MyD₃ x)][∀ g : MyD₃ , Fintype <| fixedBy (n7 n) g]
variable [Fintype Ψ][Fintype (n7 n)]

/- The set of points of (n7 n) fixed under group action by r 0 is the entirety of (n7 n) -/
lemma r0_fixed : MulAction.fixedBy (n7 n) (r 0) = Set.univ := by
simp [MulAction.fixedBy]
have r0_id (y : n7 n) : r 0 • y = y := by rfl
simp_all

/-The cardinality of set fix(r 0) is n⁷. An issue arises due to (n7 n) being a type not a set so cardinality is not defined -/
lemma r0_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (r 0)) = n^7 := by
rw [r0_fixed]
rw [Set.univ]
sorry

/- Demonstration that an ordered list in (n7 n) with form (a, a, a, b, b, b, c) is fixed under group action by r 1-/
lemma r1_fix_demonstration (a1 b1 c1 : n_set n) : ((a1, a1, a1, b1, b1, b1, c1) : n7 n) ∈ MulAction.fixedBy (n7 n) (r 1) := by
simp [MulAction.fixedBy]
constructor

/- The set of ordered lists with form (a, a, a, b, b, b, c) is the fix(r 1)-/
lemma r1_fixed : MulAction.fixedBy (n7 n) (r 1) =
{(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3}:= by
have form_imp_fix (x : n7 n) :
x ∈ {(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3} → x ∈ MulAction.fixedBy (n7 n) (r 1) := by
  intro hx
  refine MulAction.mem_fixedBy.mpr ?_
  sorry
have nform_imp_nfix (x : n7 n) :
 ¬ (x ∈ {(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3}) → ¬(x ∈ MulAction.fixedBy (n7 n) (r 1)) := by
  sorry
have form_iff_fix (x : n7 n) :
x ∈ {(a1, a2, a3, b1, b2, b3, c1) : (n7 n) | a1 = a2 ∧ a1 = a3 ∧ b1 = b2 ∧ b1 = b3} ↔ x ∈ MulAction.fixedBy (n7 n) (r 1) := by
  constructor
  exact form_imp_fix x
  contrapose
  exact nform_imp_nfix x
sorry

/- The cardinality of fix(r 1) is n³ -/
lemma r1_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (r 1)) = n^3 := by
rw [r1_fixed]
sorry

/- Repeated process of obtaining the cardinalities of fix(g) for all g in MyD₃ for application of Burnside's Lemma -/

-- lemma r2_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (r 2)) = n^3 := by
-- sorry

-- lemma sr0_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (sr 0)) = n^5 := by
-- sorry

-- lemma sr1_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (sr 1)) = n^5 := by
-- sorry

-- lemma sr2_fixed_card : Nat.card (MulAction.fixedBy (n7 n) (sr 0)) = n^5 := by
-- sorry

/- The finite sum of the cardinalities of fix(g) as g varies across MyD₃ is n⁷ + 3n⁵ + 2*n^3 -/
lemma action_fix_sum  : ∑ g : MyD₃,  Fintype.card (MulAction.fixedBy (n7 n) g) = n^7 + 3*n^5 + 2*n^3 := by
sorry

/- The cardinality of the set of orbits of MyD₃ acting on (n7 n) is proven via the Burnside Lemma to be
(n⁷ + 3n⁵ + 2*n^3)/6. In the context of the colouring puzzle, this corresponds to the number of unique colourings
of the triangle's 7 sections when there are n colours available. -/
theorem colouring_card [Fintype Ψ] : Fintype.card (Ψ) = (1/6)*(n^7 + 3*n^5 + 2*n^3) := by
rw [burnside_lemma]
rw [action_fix_sum]
rw [My_D₃_card]
