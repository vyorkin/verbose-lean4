import Verbose.Tactics.By
import Verbose.Russian.Common
import Verbose.Russian.TokenSupport

open Lean Verbose.Russian

-- NB: see Verbose/Russian/TokenSupport.lean. Unlike English/French, the "such that"
-- connective before the goal in "it suffices to prove, что" is always required (not
-- optional) here, since dropping it would also drop the comma Russian grammar requires.
declare_ru_tokens "По" "получаем" "выбираем" "достаточно" "доказать," "что"

elab "По " e:maybeAppliedRU " получаем " colGt news:newStuffRU : tactic => do
obtainTac (← maybeAppliedRUToTerm e) (newStuffRUToArray news)

elab "По " e:maybeAppliedRU " выбираем " colGt news:newStuffRU : tactic => do
chooseTac (← maybeAppliedRUToTerm e) (newStuffRUToArray news)

elab "По " e:maybeAppliedRU " достаточно доказать, что " colGt arg:term : tactic => do
bySufficesTac (← maybeAppliedRUToTerm e) #[arg]

elab "По " e:maybeAppliedRU " достаточно доказать, что " colGt args:sepBy(term, " и ") : tactic => do
bySufficesTac (← maybeAppliedRUToTerm e) args.getElems

elab "strong_assumption" : tactic => assumption'

macro "гипотеза" : term => `(by strong_assumption)

lemma le_le_of_abs_le {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α} : |a| ≤ b → -b ≤ a ∧ a ≤ b := abs_le.1

lemma le_le_of_max_le {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

implement_endpoint (lang := ru) cannotGet : CoreM String := pure "Не удалось это получить."

implement_endpoint (lang := ru) theName : CoreM String := pure "Имя"

implement_endpoint (lang := ru) needName : CoreM String :=
pure "Нужно указать имя для выбираемого объекта."

implement_endpoint (lang := ru) wrongNbGoals : CoreM String :=
pure s!"Здесь не так много утверждений для проверки."

implement_endpoint (lang := ru) doesNotApply (fact : Format) : CoreM String :=
pure s!"Не удалось применить {fact}."

implement_endpoint (lang := ru) couldNotInferImplVal (val : Name) : CoreM String :=
pure s!"Не удалось вывести неявное значение для {val}."

implement_endpoint (lang := ru) alsoNeedCheck (fact : Format) : CoreM String :=
pure s!"Также нужно проверить {fact}"

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

setLang ru

example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  По h применённый к 0 получаем h₀
  exact h₀

example (P : Nat → Nat → Prop) (h : ∀ n k, P n (k+1)) : P 0 1 := by
  По h применённый к 0 и 0 получаем (h₀ : P 0 1)
  exact h₀

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  По h получаем k такой, что (H : n = 2*k)
  trivial

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  По h получаем k такой, что H
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  По h получаем (hP : P) (hQ : Q)
  exact hQ

example (x : ℝ) (h : |x| ≤ 3) : True := by
  По h получаем (h₁ : -3 ≤ x) (h₂ : x ≤ 3)
  trivial

example (n p q : ℕ) (h : n ≥ max p q) : True := by
  По h получаем (h₁ : n ≥ p) (h₂ : n ≥ q)
  trivial

noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  По h выбираем g такой, что (H : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  По h выбираем g такой, что (H : ∀ (y : ℕ), g y ∈ A) и (H' : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  По h выбираем g такой, что (H : ∀ (y : ℕ), g y + 0 ∈ A) и (H' : ∀ (y : ℕ), f (g y) = y)
  exact g

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  По h достаточно доказать, что P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  По h достаточно доказать, что P
  exact гипотеза

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  По h достаточно доказать, что P и R
  exact hP
  exact hR

set_option linter.unusedVariables false in
example (P Q : Prop) (h : ∀ n : ℕ, P → Q) (h' : P) : Q := by
  success_if_fail_with_msg "Не удалось применить h 0 1."
    По h применённый к 0 и 1 достаточно доказать, что P
  По h применённый к 0 достаточно доказать, что P
  exact h'

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  По h применённый к 1 достаточно доказать, что 1 > 0
  norm_num

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  По h достаточно доказать, что 1 > 0
  norm_num

example {P Q R : ℕ → Prop} {n k l : ℕ} (h : ∀ k l, P k → Q l → R n) (hk : P k) (hl : Q l) :
    R n := by
  success_if_fail_with_msg "Также нужно проверить Q ?l"
    По h достаточно доказать, что P k
  По h достаточно доказать, что P k и Q l
  exact hk
  exact hl

set_option linter.unusedVariables false in
example (n : Nat) (h : ∃ n : Nat, n = n) : True := by
  success_if_fail_with_msg "Имя n уже используется"
    По h получаем n такой, что H
  trivial
