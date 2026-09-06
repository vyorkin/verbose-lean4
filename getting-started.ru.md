# Начало работы

Этот документ предполагает, что вы уже установили Lean.
См. https://lean-lang.org/lean4/doc/quickstart.html,
если вам нужна помощь с этим.

Чтобы использовать Verbose Lean в своём преподавании, вам нужно создать
Lean-проект. Это можно сделать через меню Lean в VSCode или набрав в
терминале `lake new teaching lib` — так будет создана папка `teaching` со
стандартной структурой Lean-проекта (не используйте в имени папки никаких
экзотических символов).

Вам нужно убедиться, что ваш проект использует ту же версию Lean, что и
Verbose Lean. Для этого можно скопировать содержимое файла
[lean-toolchain](https://github.com/PatrickMassot/verbose-lean4/blob/master/lean-toolchain)
из Verbose Lean в файл lean-toolchain вашего проекта (этот файл автоматически
создаётся командой `lake init` в корневой папке вашего проекта).

Затем нужно подключить библиотеку в вашем lake-файле.
Это значит, что в конец `lakefile.toml` вашего проекта нужно добавить:
```
[[require]]
name = "verbose"
git = "https://github.com/PatrickMassot/verbose-lean4.git"
rev = "master"
```

Важное замечание на случай, если у вас уже был существующий проект:
Verbose Lean сам подключит Mathlib, поэтому ваш `lakefile.lean` *не должен*
содержать строку `require mathlib`, иначе вы можете столкнуться с конфликтом
версий.

После добавления указанного выше `require` нужно выполнить
`lake update verbose` из папки вашего проекта.
Это обновит ваш файл `lake-manifest.json` и скачает Verbose Lean со всеми
его зависимостями.
Это большая загрузка, поскольку она включает скомпилированный Mathlib.

Если вы используете имя `teaching`, то теперь в вашей папке `teaching` есть
папка `Teaching`, куда попадают все ваши Lean-файлы. В ней также есть файл
`Teaching.lean`, который должен импортировать все файлы из папки `Teaching`,
которые вы хотите, чтобы `lake build` собирал (обычно это все файлы, кроме
одноразовых черновых файлов). Учтите, что имя Lean-файла, начинающееся с
цифры, доставляет одни неприятности.

Теперь вам нужно создать хотя бы один файл-«учительскую» библиотеку, который
импортирует Verbose, настраивает её и содержит определения, с которыми вы
хотите работать. После этого вы можете создавать файлы для студентов с
пояснениями и упражнениями.

Например, вы можете создать в папке `Teaching` файл `Math101.lean`
следующего содержания:
```lean
import Mathlib.Topology.Instances.Real.Lemmas
import Verbose.English.All

open Verbose English

-- Let’s define mathematical notions here

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- and some nice notation

notation3:50 f:80 " is continuous at " x₀ => continuous_function_at f x₀
notation3:50 u:80 " converges to " l => sequence_tendsto u l

-- Now configure Verbose Lean 
-- (those configuration commands are explained elsewhere)

configureUnfoldableDefs continuous_function_at sequence_tendsto 

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros 

useDefaultDataProviders

useDefaultSuggestionProviders
```

и файл `HomeWork1.lean` следующего содержания:

```lean
import Teaching.Math101

Example "Continuity implies sequential continuity"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
Proof:
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix ε > 0
  Since f is continuous at x₀ and ε > 0 we get δ such that
    (δ_pos : δ > 0) and (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  Since u converges to x₀ and δ > 0 we get N such that Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  Since ∀ n ≥ N, |u n - x₀| ≤ δ and n ≥ N we get h : |u n - x₀| ≤ δ
  Since ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε and |u n - x₀| ≤ δ we conclude that |f (u n) - f x₀| ≤ ε 
QED
```

Если процесс установки прошёл успешно, Lean должен без проблем обработать
эти файлы. После этого вы можете постепенно узнавать больше об этой
библиотеке.
