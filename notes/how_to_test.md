# How to Test

Run all tests via `spago test`

The files `src/Test/Example/*.purs` define example programs that are used for
testing.

## Test Completion

In `src/Test/TestCompletion.purs`, there is a function `testAllCompletions`
that, given a term and its type, via a traversal at each term cursor location
applies every available completion. So, it's basically a 1-depth fuzz over all
the edits you can do starting with the given program. When run, it prints the
tested term, type, term cursor path, and completion.

Completion tests require a value of the type `Term /\ Type`. See
`src/Test/Example/Example1.purs` for examples.

To add an example to the completion test suite, add it to the array use in
`Test.TestCompletion.main`
