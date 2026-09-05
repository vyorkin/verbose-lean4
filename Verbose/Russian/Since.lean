import Verbose.Tactics.Since
import Verbose.Russian.Common
import Verbose.Russian.TokenSupport
import Lean

namespace Verbose.Russian

open Lean Elab Tactic

-- NB: multi-word literal atoms are split into individual whitespace-separated word
-- tokens (see Verbose/Russian/TokenSupport.lean), so every word below (with its
-- attached punctuation) is registered separately, never as a combined phrase.
declare_ru_tokens "Поскольку" "Так" "как" "получаем" "получаем," "значит" "наконец"
  "заключаем," "что" "выбираем" "достаточно" "доказать," "Достаточно"
  "Различаем" "случаи" "или"

elab ("Поскольку " <|> "Так как ") facts:factsRU " получаем " colGt news:newObjectNameLessRU : tactic => do
  let newsT ← newObjectNameLessRUToTerm news
  let news_patt := newObjectNameLessRUToRCasesPatt news
  let factsT := factsRUToArray facts
  sinceObtainTac newsT news_patt factsT

declare_syntax_cat thenConcludeRU
syntax " наконец заключаем, что " term : thenConcludeRU

def thenConcludeRUtoTerm : TSyntax `thenConcludeRU → Term
| `(thenConcludeRU|наконец заключаем, что $t:term) => t
| _ => default

elab ("Поскольку " <|> "Так как ") facts:factsRU " получаем, что " news:sepBy1(factsRU, " значит ") concl?:(thenConcludeRU)? : tactic =>
  withMainContext do
  let newsArr := news.getElems
  let factsTArr := (#[facts] ++ newsArr).map factsRUToArray
  let newsTArr ← liftM <| (#[facts] ++ newsArr).mapM factsRUToTypeTerm
  let conclT? := if let some x := concl? then some (thenConcludeRUtoTerm x) else none
  multipleSinceObtainTac factsTArr newsTArr conclT?

elab ("Поскольку " <|> "Так как ") facts:factsRU " заключаем, что " concl:term : tactic => do
  let factsT := factsRUToArray facts
  sinceConcludeTac concl factsT

elab ("Поскольку " <|> "Так как ") fact:term " выбираем "  colGt news:newObjectNameLessRU : tactic => do
  let news := newObjectNameLessRUToArray news
  sinceChooseTac fact news

elab ("Поскольку " <|> "Так как ") facts:factsRU " достаточно доказать, что " newGoals:factsRU : tactic => do
  let factsT := factsRUToArray facts
  let newGoalsT := factsRUToArray newGoals
  sinceSufficesTac factsT newGoalsT

elab "Достаточно доказать, что " newGoals:factsRU : tactic => do
  let newGoalsT := factsRUToArray newGoals
  sinceSufficesTac #[] newGoalsT

elab "Различаем случаи " factL:term " или " factR:term : tactic => do
  sinceDiscussTac factL factR

implement_endpoint (lang := ru) unusedFact (fact : String) : TacticM String :=
  pure s!"Здесь не нужно знать, что {fact}."

setLang ru

set_option linter.unusedVariables false

example (f : ℝ → ℝ) (hf : ∀ x y, f x = f y → x = y) (x y : ℝ) (hxy : f x = f y) : x = y := by
  Поскольку ∀ x y, f x = f y → x = y и f x = f y заключаем, что x = y

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Поскольку ∃ k, n = 2*k получаем k такой, что n = 2*k
  trivial

example (n : Nat) (h : ∃ k ≥ 1, n = 2*k) : True := by
  Поскольку ∃ k ≥ 1, n = 2*k получаем k такой, что k ≥ 1 и n = 2*k
  trivial

example (n : Nat) (h : ∃ k ≥ 1, n = 2*k ∧ k ≠ 0) : True := by
  Поскольку ∃ k ≥ 1, n = 2*k ∧ k ≠ 0 получаем k такой, что k ≥ 1, n = 2*k и k ≠ 0
  trivial

example (n : Nat) (h : ∃ (k l : Nat), n = k + l) : True := by
  Поскольку ∃ (k l : Nat), n = k + l получаем k и l такие, что n = k + l
  trivial

example (n : Nat) (h : ∃ (k l : Nat), n = k + l ∧ k = 1) : True := by
  Поскольку ∃ (k l : Nat), n = k + l ∧ k = 1 получаем k и l такие, что n = k + l и k = 1
  trivial

example (n : Nat) (h : ∃ (k l : Nat), n = k + l ∧ k = 1 ∧ l = 2) : True := by
  Поскольку ∃ (k l : Nat), n = k + l ∧ k = 1 ∧ l = 2 получаем k и l такие, что n = k + l, k = 1
    и l = 2
  trivial

example (n N : Nat) (hn : n ≥ N) (h : ∀ n ≥ N, ∃ k, n = 2*k) : True := by
  success_if_fail_with_msg "Здесь не нужно знать, что n ≥ n."
    Поскольку ∀ n ≥ N, ∃ k, n = 2*k, n ≥ N и n ≥ n получаем k такой, что n = 2*k
  Поскольку ∀ n ≥ N, ∃ k, n = 2*k и n ≥ N получаем k такой, что n = 2*k
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Поскольку P ∧ Q получаем, что P и Q
  exact hQ

example (P Q R S : Prop) (h : P ↔ R) (h' : (Q → R) → S) : (Q → P) → S := by
  Поскольку P ↔ R и (Q → R) → S заключаем, что (Q → P) → S

example (P Q R S : Prop) (h : P ↔ R) (h' : (Q → R) → S) : (Q → P) → S := by
  Поскольку R ↔ P и (Q → R) → S заключаем, что (Q → P) → S

example (n : Nat) (P : Nat → Prop) (Q : ℕ → ℕ → Prop) (h : P n ∧ ∀ m, Q n m) : Q n n := by
  Поскольку P n ∧ ∀ m, Q n m получаем, что ∀ m, Q n m
  apply hQn

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : True := by
  Поскольку ∀ n ≥ 3, P n и n ≥ 3 получаем, что P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Поскольку ∀ n ≥ 3, P n ∧ Q n и n ≥ 3 получаем, что P n и Q n
  trivial

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : P n := by
  Поскольку ∀ n ≥ 3, P n и n ≥ 3 заключаем, что P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : P n := by
  Поскольку ∀ n ≥ 3, P n ∧ Q n и n ≥ 3 заключаем, что P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Поскольку ∀ n ≥ 3, P n ∧ Q n и n ≥ 3 получаем, что P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n) (h' : ∀ n ≥ 3, Q n) : True := by
  Поскольку ∀ n ≥ 3, P n, ∀ n ≥ 3, Q n и n ≥ 3 получаем, что P n и Q n
  trivial

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Поскольку P → Q достаточно доказать, что P
  exact h'

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Поскольку P → R → Q достаточно доказать, что P и R
  exact hP
  exact hR

set_option linter.unusedTactic false in
example (P : ℝ → Prop) (h : ∀ x > 0, P x)  : P 1 := by
  Поскольку 1 > 0 и ∀ x > 0, P x получаем, что P 1
  guard_hyp_nums 3
  exact hP

set_option linter.unusedTactic false in
example (P Q : ℝ → Prop) (h : ∀ x > 0, P x → Q x) (h' : P 1) : Q 1 := by
  Поскольку 1 > 0 и ∀ x > 0, P x → Q x достаточно доказать, что P 1
  guard_hyp_nums 5
  exact h'

example (P Q R S : Prop) (h : P → R → Q → S) (hP : P) (hR : R) (hQ : Q) : S := by
  Поскольку P → R → Q → S достаточно доказать, что P, R и Q
  exact hP
  exact hR
  exact hQ

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q := by
  Поскольку P ↔ Q достаточно доказать, что P
  exact hP

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q ∧ True:= by
  constructor
  Поскольку P ↔ Q достаточно доказать, что P
  exact hP
  trivial

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  success_if_fail_with_msg "
Не удалось доказать:
P : ℕ → Prop
x y : ℕ
GivenFact_0 : x = y
⊢ P y"
    Поскольку x = y получаем, что P y
  Поскольку x = y и P x получаем, что P y
  exact hPy

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Поскольку x = y и P x заключаем, что P y

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Поскольку x = y достаточно доказать, что P x
  exact h'

example (ε : ℝ) (ε_pos : ε > 0) : ε ≥ 0 := by
  Поскольку ε > 0 заключаем, что ε ≥ 0

example (f : ℕ → ℕ) (x y : ℕ) (h : x = y) : f x ≤ f y := by
  Поскольку x = y заключаем, что f x ≤ f y

configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le Classical.em

example (P Q : Prop) (h : P ∨ Q) : True := by
  Различаем случаи P или Q
  all_goals tauto

example (P Q : Prop) (h : P ∨ Q) : True := by
  Различаем случаи Q или P
  all_goals tauto

example (P : Prop) : True := by
  Различаем случаи P или ¬ P
  all_goals tauto

example (x y : ℕ) : True := by
  Различаем случаи x ≤ y или x > y
  all_goals tauto

example (x y : ℕ) : True := by
  Различаем случаи x = y или x ≠ y
  all_goals tauto

example (x y : ℕ) (h : x ≠ y) : True := by
  Различаем случаи x < y или x > y
  all_goals tauto

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by
  success_if_fail_with_msg "Не удалось доказать:
ε : ℝ
SufficientFact_0 : ε < 0
⊢ ε ≥ 0"
    Достаточно доказать, что ε < 0
  Достаточно доказать, что ε > 0
  exact h

lemma le_le_of_max_le' {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

configureAnonymousFactSplittingLemmas le_max_left le_max_right le_le_of_max_le' le_of_max_le_left le_of_max_le_right

example (n a b : ℕ) (h : n ≥ max a b) : True := by
  Поскольку n ≥ max a b получаем, что n ≥ a и n ≥ b
  trivial

example (n a b : ℕ) (h : n ≥ max a b) : True := by
  Поскольку n ≥ max a b получаем, что n ≥ a
  trivial

example (n a b : ℕ) (h : n ≥ max a b) (P : ℕ → Prop) (hP : ∀ n ≥ a, P n) : P n := by
  Поскольку ∀ n ≥ a, P n и n ≥ a заключаем, что P n

set_option linter.unusedVariables false in
example (a b : ℕ) (P : ℕ → Prop) (h : ∀ n ≥ a, P n) : True := by
  Поскольку ∀ n ≥ a, P n и max a b ≥ a получаем, что P (max a b)
  trivial

example (a b : ℝ) (h : a + b ≤ 3) (h' : b ≥ 0) : b*(a + b) ≤ b*3 := by
  success_if_fail_with_msg "
Не удалось доказать:
a b : ℝ
GivenFact_0 : a + b ≤ 3
⊢ b * (a + b) ≤ b * 3"
    Поскольку a + b ≤ 3 заключаем, что b*(a + b) ≤ b*3
  Поскольку a + b ≤ 3 и b ≥ 0 заключаем, что b*(a + b) ≤ b*3

example (a b : ℝ) (hb : b = 2) : a + a*b = a + a*2 := by
  Поскольку b = 2 заключаем, что a + a*b = a + a*2

example (P Q R S T : Prop) (hPR : P ↔ R) : ((Q → R) → S) ↔ ((Q → P) → S) := by
  Поскольку P ↔ R заключаем, что ((Q → R) → S) ↔ ((Q → P) → S)

example (a k : ℤ) (h : a = 0*k) : a = 0 := by
  Поскольку a = 0*k заключаем, что a = 0

local macro_rules | `($x ∣ $y)   => `(@Dvd.dvd ℤ Int.instDvd ($x : ℤ) ($y : ℤ))

example (a : ℤ) (h : a = 0) : a ∣ 0 := by
  success_if_fail_with_msg "
Не удалось доказать:
a : ℤ
GivenFact_0 : a = 0
⊢ a ∣ 0"
    Поскольку a = 0 заключаем, что a ∣ 0
  Поскольку a = 0 достаточно доказать, что 0 ∣ 0
  use 0
  rfl

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Поскольку P и Q заключаем, что P ∧ Q

example (P Q : Prop) (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  Поскольку P → Q и Q → P заключаем, что P ↔ Q


configureAnonymousFactSplittingLemmas LogicElims

example (P Q : Prop) (hPQ : P ↔ Q) : True := by
  Поскольку P ↔ Q получаем, что P → Q и Q → P
  trivial

private lemma test_abs_le_of_le_le {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h : -b ≤ a) (h' : a ≤ b) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

private lemma test_abs_le_of_le_le' {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h' : a ≤ b) (h : -b ≤ a) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

private lemma test_abs_le_of_le_and_le {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h : -b ≤ a ∧ a ≤ b) : |a| ≤ b := abs_le.2 h

configureAnonymousGoalSplittingLemmas test_abs_le_of_le_le test_abs_le_of_le_le' test_abs_le_of_le_and_le

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Поскольку (-1 ≤ a - b ∧ a - b ≤ 1) → |a - b| ≤ 1 достаточно доказать, что -1 ≤ a - b ∧ a - b ≤ 1
  exact ⟨h, h'⟩

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Поскольку (-1 ≤ a - b ∧ a - b ≤ 1) → |a - b| ≤ 1 достаточно доказать, что -1 ≤ a - b и a - b ≤ 1
  all_goals assumption

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Поскольку -1 ≤ a - b → a - b ≤ 1 → |a - b| ≤ 1 достаточно доказать, что -1 ≤ a - b и a - b ≤ 1
  all_goals assumption

example (u v : ℕ → ℝ) (h : ∀ n, u n ≤ v n) : u 0 - 2 ≤ v 0 - 2 := by
  Поскольку ∀ n, u n ≤ v n заключаем, что u 0 - 2 ≤ v 0 - 2

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ (∀ x, P x) := by
  Достаточно доказать, что ∃ x, ¬ P x
  exact h

example (P Q : Prop) (h : ¬ P ∨ Q) : P → Q := by
  Поскольку ¬ P ∨ Q заключаем, что P → Q

example (P : Prop) (x : ℝ) (h : ¬ (P ∧ x < 0)) : P → x ≥ 0 := by
  Поскольку ¬ (P ∧ x < 0) заключаем, что P → x ≥ 0

private def foo_bar (P : Nat → Prop) := ∀ x, P x
configureUnfoldableDefs foo_bar

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ foo_bar P := by
  Достаточно доказать, что ∃ x, ¬ P x
  exact h

example (P : Nat → Prop) (h : ¬ foo_bar P) : ∃ x, ¬ P x := by
  Поскольку ¬ foo_bar P получаем, что ∃ x, ¬ P x
  exact hP

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ (∀ x, P x) := by
  Поскольку ∃ x, ¬ P x заключаем, что ¬ (∀ x, P x)

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : True := by
  Поскольку ∃ x, ¬ P x получаем, что ¬ (∀ x, P x)
  trivial

example (h : (2 : ℝ) * -42 = 2 * 42) : False := by
  -- Примечание: следующий пример не требует перебора, так как linarith
  -- находит доказательство, используя h в любом случае
  Поскольку 2 * -42 = 2 * 42 заключаем, что False

-- Следующие три примера проверяют переэлаборацию чисел как вещественных после неудачи

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Поскольку ∀ ε > 0, P ε и 1 > 0 получаем, что P 1
  exact hP

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Поскольку ∀ ε > 0, P ε и 1 > 0 заключаем, что P 1

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Поскольку ∀ ε > 0, P ε достаточно доказать, что 1 > 0
  norm_num

example (l : ℝ) (N : ℕ) (h : |(-1)^(2*N) - l| ≤ 1/2) : True := by
  Поскольку |(-1)^(2*N) - l| ≤ 1/2 и (-1)^(2*N) = (1 : ℝ) получаем, что |1 - l| ≤ 1/2
  trivial

noncomputable section
example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  Поскольку ∀ y, ∃ x, f x = y выбираем g такой, что ∀ (y : ℕ), f (g y) = y
  exact g

example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Поскольку ∀ y, ∃ x ∈ A, f x = y выбираем g такой, что ∀ (y : ℕ), g y ∈ A и ∀ (y : ℕ), f (g y) = y
  exact g

example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Поскольку ∀ y, ∃ x ∈ A, f x = y выбираем g такой, что ∀ (y : ℕ), g y + 0 ∈ A и ∀ (y : ℕ), f (g y) = y
  exact g

end

addAnonymousFactSplittingLemma lt_of_lt_of_le

example (ε : ℝ) (ε_pos : 1/ε > 0) (N : ℕ) (hN : N ≥ 1 / ε) : True := by
  Поскольку N ≥ 1/ε и 1/ε > 0 получаем, что N > 0
  trivial

example (ε : ℝ) (ε_pos : 1/ε > 0) (N : ℕ) (hN : N ≥ 1 / ε) : N > 0 := by
  Поскольку N ≥ 1/ε и 1/ε > 0 заключаем, что N > 0

addAnonymousFactSplittingLemma abs_of_pos
example (a b : ℝ) (h : a ≥ b) (h' : b > 0) : True := by
  Поскольку a ≥ b и b > 0 получаем, что a > 0 значит |a| = a
  trivial

example (a b : ℝ) (h : a ≥ b) (h' : b > 0) : |a| = a := by
  Поскольку a ≥ b и b > 0 получаем, что a > 0 наконец заключаем, что |a| = a

example (a b c d : ℝ) (h : a = b) (h': c = d) : a - c = b - d := by
  Поскольку a = b и c = d заключаем, что a - c = b - d

-- Регрессионный тест на превышение лимита эвристик в simpa
example (a b c : ℝ) (h : a = b) (h' : b = b * c) : b - b = b - b * c := by
  Поскольку b = b * c заключаем, что b - b = b - b * c

end Verbose.Russian
