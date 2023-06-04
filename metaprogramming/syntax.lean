/-
## Exercises

1. Create an "urgent minus 💀" notation such that `5 * 8 💀 4` returns `20`, and `8 💀 6 💀 1` returns `3`.

**a)** Using `notation` command.  
**b)** Using `infix` command.  
**c)** Using `syntax` command.  

Hint: multiplication in Lean 4 is defined as `infixl:70 " * " => HMul.hMul`.

2. Consider the following syntax categories: `term`, `command`, `tactic`; and 3 syntax rules given below. Make use of each of these newly defined syntaxes.

```
  syntax "good morning" : term
  syntax "hello" : command
  syntax "yellow" : tactic
```

3. Create a `syntax` rule that would accept the following commands:

- `red red red 4`
- `blue 7`
- `blue blue blue blue blue 18`

(So, either all `red`s followed by a number; or all `blue`s followed by a number; `red blue blue 5` - shouldn't work.)

Use the following code template:

```
syntax (name := colors) ...
-- our "elaboration function" that infuses syntax with semantics
@[command_elab colors] def elabColors : CommandElab := λ stx => Lean.logInfo "success!"
```

4. Mathlib has a `#help option` command that displays all options available in the current environment, and their descriptions. `#help option pp.r` will display all options starting with a "pp.r" substring.

Create a `syntax` rule that would accept the following commands:

- `#better_help option`
- `#better_help option pp.r`
- `#better_help option some.other.name`

Use the following template:

```
syntax (name := help) ...
-- our "elaboration function" that infuses syntax with semantics
@[command_elab help] def elabHelp : CommandElab := λ stx => Lean.logInfo "success!"
```

5. Mathlib has a ∑ operator. Create a `syntax` rule that would accept the following terms:

- `∑ x in { 1, 2, 3 }, x^2`
- `∑ x in { "apple", "banana", "cherry" }, x.length`

Use the following template:

```
import Std.Classes.SetNotation
import Std.Util.ExtendedBinder
syntax (name := bigsumin) ...
-- our "elaboration function" that infuses syntax with semantics
@[term_elab bigsumin] def elabSum : TermElab := λ stx tp => return mkNatLit 666
```

Hint: use the `Std.ExtendedBinder.extBinder` parser.
Hint: you need Std4 installed in your Lean project for these imports to work.
-/