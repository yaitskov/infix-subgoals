ACL2 infix subgoals book
========================

This ACL2 book provides a custom formatter for ACL2 logical
propositions.  The formatter intercepts subgoals emitted by commands
such as `thm` and `defthm` during the proof process.

ACL2 once had a full-fledge infix mode, but it was deprecated and
removed many years ago. After working with the Dafny and Rocq provers,
I found it difficult, as a fresh eye reader, to recognize conjuctures
that were not written by me and were formatted in conventional Lisp
style. Beyond these subjective concerns - infix notation is
significatnly more compact than the classical prefix form. While
proving simple theorems, I found that infix syntax appeared less
cluttered and easier to scan.

That said, I am not entirely certain that infix notation is superior
in all contexts. I anticipate that parenthesis-oriented style may work
better in a production environment, as it can facilitate navigation
across large expressions.

# Example
To give an idea of what the book does, compare the following snippet expressed in Lisp
notation with the same snippet written in infix notation (inspired by Haskell and Dafny).


``` common-lisp
(implies (and (consp l)
                  (natp s)
                  (natp x)
                  (< s (len l))
                  (<= s x)
                  (< x (len l))
                  (equal (nth x l) " "))
             (equal (nth s l) " "))
```

``` haskell
CONSP L ∧ INTEGERP S ∧ 0 ≤ S ∧ INTEGERP X ∧ 0 ≤ X ∧ S < LEN L ∧ S ≤ X ∧ X < LEN L ∧ L[X] = " " → L[S] = " "
```

# Usage

## Interactive (REPL) mode

``` common-lisp
(ld "./infix-subgoals.lisp")
```

The book installs `acl2::post-untranslate-hook` hook automatically upon loading.
