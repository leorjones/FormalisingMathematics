import Mathlib.Tactic

variable (n : ℕ)

def n_set : Set ℕ := Finset.range n

variable (a1 a2 a3 b1 b2 b3 c1 : n_set n)

def n7 := n_set (n) × n_set (n) × n_set (n) × n_set (n) ×  n_set (n) × n_set (n) × n_set (n)

def example_element : n7 n := (a1, a2, a3, b1, b2, b3, c1)

inductive D₃
| e : D₃     -- Identity
| r₀ : D₃    -- Rotation by 120 degrees clockwise
| r₁  : D₃   -- Rotation by 240 degrees clockwise
| s₀  : D₃   -- Reflect about line through top vertex
| s₁  : D₃   -- Reflect about line through left vertex
| s₂  : D₃   -- Reflect about line through right vertex

structure MyFiniteGroup :=
(elements : Type)
(mult_table : (elements ×  elements) → elements)
(table_prop : ∀ (a b : elements), mult_table (a, b) ∈ [e, r₀, r₁, s₀, s₁, s₂])

/- Would love to use indexing such as by naming id as r₀ and having the others
as r₁ and r₂ so i can use rᵢ*rⱼ = r(i+j mod 3) and so on -/
def mult_table : (D₃ × D₃) → D₃
| (D₃.e, g) => g
| (g, D₃.e) => g
| (D₃.r₀, D₃.r₀) => D₃.r₁
| (D₃.r₀, D₃.r₁) => D₃.e
| (D₃.r₀, D₃.s₀) => D₃.s₂
| (D₃.r₀, D₃.s₁) => D₃.s₀
| (D₃.r₀, D₃.s₂) => D₃.s₁
| (D₃.r₁, D₃.r₀) => D₃.e
| (D₃.r₁, D₃.r₁) => D₃.r₀
| (D₃.r₁, D₃.s₀) => D₃.s₁
| (D₃.r₁, D₃.s₁) => D₃.s₂
| (D₃.r₁, D₃.s₂) => D₃.s₀
| (D₃.s₀, D₃.r₀) => D₃.s₁
| (D₃.s₀, D₃.r₁) => D₃.s₂
| (D₃.s₀, D₃.s₀) => D₃.e
| (D₃.s₀, D₃.s₁) => D₃.r₀
| (D₃.s₀, D₃.s₂) => D₃.r₁
def rotation_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a3, a1, b2, b3, b1, c1)

def reflection_0_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a1, a3, a2, b3, b2, b1, c1)

def reflection_1_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a3, a2, a1, b2, b1, b3, c1)

def reflection_2_funct : n7 n → n7 n
| ⟨a1, a2, a3, b1, b2, b3, c1 ⟩ => (a2, a1, a3, b1, b3, b2, c1)

def myaction2: D₃ → (n7 n → n7 n)
| D₃.e => id
| D₃.r₀ => rotation_funct n
| D₃.r₁ => (rotation_funct n) ∘ (rotation_funct n)
| D₃.s₀ => reflection_0_funct n
| D₃.s₁ => reflection_1_funct n
| D₃.s₂ => reflection_2_funct n

lemma identity_action (x : n7 n) : myaction2 n D₃.e x = x := by exact rfl

lemma compatibility_action (g1 g2 : D₃) (x : n7 n) :
  myaction2 n g1 (myaction2 n g2 x) = myaction2 n (g1 * g2) x := by
sorry

instance : mul_action D₃ n7 :=
