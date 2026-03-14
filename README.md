# Lean Snippets

> A curated collection of functional programming patterns and advanced techniques implemented in **Lean 4**

---

## Overview

This repository showcases various functional programming concepts, from lazy evaluation and continuations to category theory-inspired patterns. Each snippet is self-contained and demonstrates idiomatic Lean 4 code.

## Snippets

### Lazy Evaluation & Circular Programming

| File | Description |
|------|-------------|
| [LazyStream.lean](Snippets/LazyStream.lean) | Infinite lazy streams with `cons`, `take`, `skip`, `map`, and `unfold` operations |
| [LazyFix.lean](Snippets/LazyFix.lean) | Lazy fixed-point combinator for defining recursive values (e.g., infinite `ones` stream) |
| [LazyBFSTreeLabeling.lean](Snippets/LazyBFSTreeLabeling.lean) | Breadth-first tree labeling using circular programming — labels tree nodes in BFS order using lazy self-reference |
| [LazyGenName.lean](Snippets/LazyGenName.lean) | Fresh name generation using circular programs, based on *"Using Circular Programs for Higher-Order Syntax"* |
| [Repmin.lean](Snippets/Repmin.lean) | Bird's classic *repmin* problem — replaces all leaves with the minimum value in a single traversal |
| [LoebSpreadsheet.lean](Snippets/LoebSpreadsheet.lean) | Löb's theorem as a spreadsheet evaluator — cells can reference other cells, inspired by [sigfpe's blog](http://blog.sigfpe.com/2006/11/from-l-theorem-to-spreadsheet.html) |
| [LazyTests.lean](Snippets/LazyTests.lean) | Tests for verifying thunk identity and caching behavior |

### Continuations & Control Flow

| File | Description |
|------|-------------|
| [ContT.lean](Snippets/ContT.lean) | Continuation monad transformer with `shift`, `reset`, and `callCC` operators |
| [YinYang.lean](Snippets/YinYang.lean) | The famous *Yin-Yang puzzle* — a mind-bending demonstration of first-class continuations |
| [ZipperTraversable.lean](Snippets/ZipperTraversable.lean) | Zippers via delimited continuations — traverse and update data structures incrementally |

### Interpreters & Languages

| File | Description |
|------|-------------|
| [LittleScheme.lean](Snippets/LittleScheme.lean) | A minimal Scheme interpreter for *"The Little Schemer"* with lexer, parser, and evaluator |
| [SystemFPHOAS.lean](Snippets/SystemFPHOAS.lean) | Intrinsically typed PHOAS fragment of System F, with pretty-printing and denotation for the executable variable-instantiation fragment |
| [Unlambda.lean](Snippets/Unlambda.lean) | Interpreter for [Unlambda](http://www.madore.org/~david/programs/unlambda/), the esoteric combinator-based language |

### Category Theory & Abstractions

| File | Description |
|------|-------------|
| [Classes.lean](Snippets/Classes.lean) | `Traversable` typeclass definition with `List` instance |
| [Naperian.lean](Snippets/Naperian.lean) | Naperian functors (representable functors) with logarithm types — includes matrix transpose example |

### Utilities

| File | Description |
|------|-------------|
| [MyMacros.lean](Snippets/MyMacros.lean) | Custom `lazy` syntax macro for cleaner thunk creation |

---

## Getting Started

### Prerequisites

- [Lean 4](https://lean-lang.org/) and [Lake](https://github.com/leanprover/lake) build system

### Building

```bash
lake build
```

### Running Examples

Most files include `#eval` commands that can be executed directly in the Lean editor or via:

```bash
lake env lean Snippets/<filename>.lean
```

`SystemFPHOAS.lean` currently supports polymorphism together with type
instantiation at bound type variables. Arbitrary compound type instantiation is
the main missing piece between the current executable kernel and full System F.

---

## References

- [Parametric Higher-Order Abstract Syntax (Lean example)](https://lean-lang.org/examples/1900-1-1-parametric-higherorder-abstract-syntax/)
- [Using Circular Programs for Higher-Order Syntax](https://emilaxelsson.github.io/documents/axelsson2013using.pdf)
- [From Löb's Theorem to Spreadsheet Evaluation](http://blog.sigfpe.com/2006/11/from-l-theorem-to-spreadsheet.html)
- [Naperian Functors](https://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/aplicative.pdf)
- [Zipper via Traversable](http://okmij.org/ftp/continuations/zipper.html#traversable)
- [Unlambda Programming Language](http://www.madore.org/~david/programs/unlambda/)

---

## License

See [LICENSE](LICENSE) for details.
