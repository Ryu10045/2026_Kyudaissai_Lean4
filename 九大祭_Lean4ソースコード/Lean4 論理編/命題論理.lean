import Mathlib.Data.Set.Basic
/-! # 命題論理 -/
open Set
namespace myProp

inductive formula (P : Type u) where
  | atom : P → formula P
  | falsum : formula P
  | imp : formula P → formula P → formula P
prefix:99 "#" => formula.atom
notation:100 "⊥" => formula.falsum
infixr:95 " -> " => formula.imp
variable {P : Type u}

def not : formula P → formula P := fun φ => φ -> ⊥
prefix:98 "~" => not
def or : formula P → formula P → formula P := fun φ ψ => ~φ -> ψ
infixl:96 " || " => or
def and : formula P → formula P → formula P := fun φ ψ => ~(φ -> ~ψ)
infixl:97 " && " => and
def iff : formula P → formula P → formula P := fun φ ψ => (φ -> ψ) && (ψ -> φ)
infix:94 " <-> " => iff

--  1. 意味論

abbrev valuation P := P → Prop
def val (V : valuation P) : formula P → Prop
  | formula.atom p => V p
  | formula.falsum => False
  | formula.imp φ ψ => (val V φ) → (val V ψ)
notation:90 V "[" φ "]" => val V φ
variable (V : valuation P) (φ ψ θ : formula P)

@[simp] theorem val_atom (p : P) : V[#p] = V p := rfl
@[simp] theorem val_falsum : V[⊥] = False := rfl
@[simp] theorem val_imp : V[φ -> ψ] = (V[φ] → V[ψ]) := rfl
@[simp] theorem val_not : V[~φ] = ¬V[φ] := rfl
@[simp] theorem val_or : V[φ || ψ] = (V[φ] ∨ V[ψ]) := by simp [or, or_iff_not_imp_left]
@[simp] theorem val_and : V[φ && ψ] = (V[φ] ∧ V[ψ]) := by simp [and]
@[simp] theorem val_iff : V[φ <-> ψ] = (V[φ] ↔ V[ψ]) := by simp [iff, iff_iff_implies_and_implies]

abbrev theory (P : Type u) := Set (formula P)
def satisfy (T : theory P) (φ : formula P) : Prop :=
    ∀ V : valuation P, (∀ ψ ∈ T, V[ψ]) → V[φ]
notation:80 T " ⊨ " φ => satisfy T φ
notation:79 "⊨ " φ => satisfy ∅ φ

variable {S T : theory P} {φ ψ θ : formula P}
theorem subset_satisfy : S ⊆ T → (S ⊨ φ) → T ⊨ φ := by
  intro hST hSφ V hT
  have hS : ∀ ψ ∈ S, V[ψ] := by
    intro ψ hψ
    exact hT ψ (hST hψ)
  exact hSφ V hS

theorem satisfy_axm1 : T ⊨ (φ -> ψ -> φ) := by
  intro _ _ h _
  exact h
theorem satisfy_axm2 : T ⊨ ((φ -> ψ -> θ) -> (φ -> ψ) -> φ -> θ) := by
  intro _ _ h1 h2 h3
  exact h1 h3 (h2 h3)
theorem satisfy_nn : T ⊨ (~~φ -> φ) := by
  intro _ _ h
  exact Classical.not_not.mp h

--  2. 構文論

inductive prove (T : theory P) : formula P → Prop where
  | assmp : ∀ φ ∈ T, prove T φ
  | axm1 : ∀ φ ψ : formula P, prove T (φ -> ψ -> φ)
  | axm2 : ∀ φ ψ θ : formula P, prove T ((φ -> ψ -> θ) -> (φ -> ψ) -> φ -> θ)
  | nn : ∀ φ : formula P, prove T (~~φ -> φ)
  | MP : ∀ φ ψ : formula P, prove T φ → prove T (φ -> ψ) → prove T ψ
notation:80 T " ⊢ " φ => prove T φ
notation:79 "⊢ " φ => prove ∅ φ

theorem assmp : φ ∈ T → T ⊢ φ := prove.assmp φ
theorem axm1 (φ ψ : formula P) : T ⊢ φ -> ψ -> φ := prove.axm1 φ ψ
theorem axm2 (φ ψ θ : formula P) : T ⊢ (φ -> ψ -> θ) -> (φ -> ψ) -> φ -> θ := prove.axm2 φ ψ θ
theorem nn (φ : formula P) : T ⊢ ~~φ -> φ := prove.nn φ
theorem MP : (T ⊢ φ) → (T ⊢ φ -> ψ) → T ⊢ ψ := prove.MP φ ψ

theorem prove_imp_self (φ : formula P) : T ⊢ φ -> φ := by
  have h1 := @axm2 P T φ (φ -> φ) φ
  have h2 := @axm1 P T φ (φ -> φ)
  have h3 := @axm1 P T φ φ
  exact MP h3 (MP h2 h1)

theorem prove_to_imp (φ : formula P) : (T ⊢ ψ) → T ⊢ φ -> ψ := by
  intro h1
  exact MP h1 (axm1 ψ φ)

theorem subset_prove : S ⊆ T → (S ⊢ φ) → T ⊢ φ := by
  intro hST hSφ
  induction hSφ with
  | assmp φ hφ => exact assmp (hST hφ)
  | axm1 => apply axm1
  | axm2 => apply axm2
  | nn => apply nn
  | MP _ _ _ _ h1 h2 => exact MP h1 h2

theorem deduction : (T ⊢ φ -> ψ) ↔ ((T ∪ {φ}) ⊢ ψ) := by
  constructor
  · intro h
    have hφ : (T ∪ {φ}) ⊢ φ := assmp (Or.inr rfl)
    have hφψ : (T ∪ {φ}) ⊢ φ -> ψ := subset_prove subset_union_left h
    exact MP hφ hφψ
  · intro h
    induction h with
    | assmp ψ h =>
      cases h with
      | inl h =>
        exact prove_to_imp φ (assmp h)
      | inr h =>
        rw [h]
        exact prove_imp_self φ
    | axm1 ψ1 ψ2 => exact prove_to_imp φ (axm1 ψ1 ψ2)
    | axm2 ψ1 ψ2 ψ3 => exact prove_to_imp φ (axm2 ψ1 ψ2 ψ3)
    | nn ψ1 => exact prove_to_imp φ (nn ψ1)
    | MP θ ψ _ _ h1 h2 => exact MP h1 (MP h2 (axm2 φ θ ψ))

theorem soundness : (T ⊢ φ) → T ⊨ φ := by
  intro h
  induction h with
  | assmp φ hφ =>
    intro _ h
    exact h φ hφ
  | axm1 => exact satisfy_axm1
  | axm2 => exact satisfy_axm2
  | nn => exact satisfy_nn
  | MP _ _ _ _ h1 h2 =>
    intro V h
    exact h2 V h (h1 V h)

end myProp
