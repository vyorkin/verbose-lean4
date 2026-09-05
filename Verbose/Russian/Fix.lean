import Verbose.Tactics.Fix
import Verbose.Russian.TokenSupport

open Lean Elab Tactic

declare_ru_tokens "Пусть₁" "Пусть"

syntax "Пусть₁ " colGt fixDecl : tactic
syntax "Пусть " (colGt fixDecl)+ : tactic

elab_rules : tactic
  | `(tactic| Пусть₁ $x:ident) => Fix1 (introduced.bare x x.getId)

elab_rules : tactic
  | `(tactic| Пусть₁ $x:ident : $type) =>
    Fix1 (introduced.typed (mkNullNode #[x, type]) x.getId type)

elab_rules : tactic
  | `(tactic| Пусть₁ $x:ident < $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.lt bound)

elab_rules : tactic
  | `(tactic| Пусть₁ $x:ident > $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.gt bound)

elab_rules : tactic
  | `(tactic| Пусть₁ $x:ident ≤ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.le bound)

elab_rules : tactic
  | `(tactic| Пусть₁ $x:ident ≥ $bound) =>
    Fix1 (introduced.related (mkNullNode #[x, bound]) x.getId intro_rel.ge bound)


elab_rules : tactic
  | `(tactic| Пусть₁ $x:ident ∈ $set) =>
    Fix1 (introduced.related (mkNullNode #[x, set]) x.getId intro_rel.mem set)

elab_rules : tactic
  | `(tactic| Пусть₁ ( $decl:fixDecl )) => do evalTactic (← `(tactic| Пусть₁ $decl:fixDecl))


macro_rules
  | `(tactic| Пусть $decl:fixDecl) => `(tactic| Пусть₁ $decl)

macro_rules
  | `(tactic| Пусть $decl:fixDecl $decls:fixDecl*) => `(tactic| Пусть₁ $decl; Пусть $decls:fixDecl*)

implement_endpoint (lang := ru) noObjectIntro : CoreM String :=
pure "Здесь нет объекта для введения."

implement_endpoint (lang := ru) noHypIntro : CoreM String :=
pure "Здесь нет предположения для введения."

implement_endpoint (lang := ru) negationByContra (hyp : Format) : CoreM String :=
pure s!"Цель уже является отрицанием, доказывать её от противного бессмысленно. \
 Можно сразу предположить {hyp}."

implement_endpoint (lang := ru) wrongNegation : CoreM String :=
pure "Это не то, что нужно предполагать от противного, даже после внесения отрицаний."

macro_rules
| `(ℕ) => `(Nat)

setLang ru

example : ∀ b : ℕ, ∀ a : Nat, a ≥ 2 → a = a ∧ b = b := by
  Пусть b (a ≥ 2)
  trivial

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Пусть (n > 0) k (l ∈ (Set.univ : Set ℕ))
  trivial

-- FIXME: The next example shows an elaboration issue
/- example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Пусть (n > 0) k (l ∈ Set.univ)
  trivial

-- while the following works
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  intro n n_pos k l (hl : l ∈ Set.univ)
  trivial
  -/

set_option linter.unusedVariables false in
example : ∀ n > 0, ∀ k : ℕ, ∀ l ∈ (Set.univ : Set ℕ), true := by
  Пусть n
  success_if_fail_with_msg "Здесь нет объекта для введения."
    Пусть h
  intro hn
  Пусть k (l ∈ (Set.univ : Set ℕ)) -- same elaboration issue here
  trivial

/- FIXME:
The next examples show that name shadowing detection does not work.

example : ∀ n > 0, ∀ k : ℕ, true := by
  Пусть (n > 0)
  success_if_fail_with_msg ""
    Пусть n
  Пусть k
  trivial


example : ∀ n > 0, ∀ k : ℕ, true := by
  Пусть n > 0
  success_if_fail_with_msg ""
    Пусть n
  Пусть k
  trivial
 -/

example (k l : ℕ) : ∀ n ≤ k + l, true := by
  Пусть n ≤ k + l
  trivial


example (A : Set ℕ) : ∀ n ∈ A, true := by
  Пусть n ∈ A
  trivial
