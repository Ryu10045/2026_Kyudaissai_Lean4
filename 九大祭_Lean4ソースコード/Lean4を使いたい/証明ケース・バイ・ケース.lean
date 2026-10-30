import Mathlib
variable ( α : Type) (p q : Prop) (r :α→Prop)
-- 無名コンストラクタを用いてもよい
example (hp : p) (hq : q) : p ∧ q := by
  exact ⟨hp, hq⟩

-- constructor を使えば，証明を 2 つに分解できる
example (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

-- 4.4 仮定に連言 (∧) を含む命題（p.36–37）
-- p の証明や q の証明を And.left や And.right で取り出すことができる
example (h : p ∧ q) : p := by
  exact And.left h

example (h : p ∧ q) : q := by
  exact And.right h

-- 次のように書いてもよい
example (h : p ∧ q) : p := by
  exact h.left

example (h : p ∧ q) : q := by
  exact h.right

-- 4.5 結論に選言 (∨) を含む命題（p.37）
-- 「または」を示すときは，Or.inl や Or.inr を用いる
example (h : p) : p ∨ q := by
  exact Or.inl h

example (h : q) : p ∨ q := by
  exact Or.inr h

-- ∨ を示す際，left や right でどちらを示すか宣言できる
example (h : p) : p ∨ q := by
  left
  exact h

example (h : q) : p ∨ q := by
  right
  exact h

-- 4.6 仮定に選言 (∨) を含む命題（p.37–38）
-- (p ∨ q) から r を示すときは，p から r と，q から r を示せればよい
example (h : p ∨ p) : p := by
  apply Or.elim h
  · intro hl
    exact hl
  · intro hr
    exact hr

-- cases や induction で分解できる
example (h : p ∨ p) : p := by
  cases h with
  | inl hl =>
      exact hl
  | inr hr =>
      exact hr

-- 4.7 結論に同値 (↔) を含む命題（p.38）
-- 「同値」も「かつ」と同様
example (h1 : p → q) (h2 : q → p) : p ↔ q := by
  exact Iff.intro h1 h2
-- 注：厳密には，(p ↔ q) と ((p → q) ∧ (q → p)) は異なる

example (h1 : p → q) (h2 : q → p) : p ↔ q := by
  constructor
  · exact h1
  · exact h2

-- 4.8 仮定に同値 (↔) を含む命題（p.38–39）
-- 仮定 (p ↔ q) から (p → q) や (q → p) を取り出す場合は，Iff.mp や Iff.mpr を用いる
example (h : p ↔ q) : p → q := by
  exact Iff.mp h

example (h : p ↔ q) : p → q := by
  exact h.mp

example (h : p ↔ q) : q → p := by
  exact Iff.mpr h

example (h : p ↔ q) : q → p := by
  exact h.mpr

-- 4.9 結論に全称 (∀) を含む命題（p.39）
-- 「任意」は「ならば」と同様に，intro で元を得ることができる
example : ∀ x : α, r x → r x := by
  intro x h -- x : α を任意にとり、r x の証明を導入する
  exact h

-- 4.10 仮定に全称 (∀) を含む命題（p.39）
example (y : α) (h : ∀ x : α, r x) : r y := by
  exact h y

-- 4.11 結論に存在 (∃) を含む命題（p.39）
-- 「存在」を示すには，Exists.intro で元と示すべき命題を与えればよい
example (a : α) : ∃ x : α, x = x := by
  exact Exists.intro a rfl

-- use を用いてもよい
example (a : α) : ∃ x : α, x = x := by
  use a

-- 4.12 仮定に存在 (∃) を含む命題（p.40）
-- 仮定に ∃ が含まれる場合は，Exists.elim を用いる
example (h : ∃ x : α, r x) : ¬ ∀ x : α, ¬ r x := by
  intro h'
  apply Exists.elim h
  intro y hy
  exact h' y hy

-- ∨ と同様，cases や induction でもよい
example (h : ∃ x : α, r x) : ¬ ∀ x : α, ¬ r x := by
  intro h'
  cases h with
  | intro y hy =>
      exact h' y hy

-- 4.13 否定 (¬) と矛盾（p.40）
example (h : p → False) : ¬p := by
  exact h

example (hp : p) (hnp : ¬p) : q := by
  exact False.elim (hnp hp)
