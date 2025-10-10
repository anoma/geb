import GebLean

/-!
# Basic Tests

This file contains basic sanity tests for the GebLean library using Lean's
built-in `#guard` command.

The `#guard` command checks that an expression evaluates to `true` at
compile time. If it fails, the build will fail.
-/

-- Test that we can import the library
#guard true
