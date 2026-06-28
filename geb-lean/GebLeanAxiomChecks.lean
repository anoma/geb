import GebLeanAxiomChecks.Unit
import GebLeanAxiomChecks.Native
import GebLeanAxiomChecks.Tests
import GebLeanAxiomChecks.Vendored

/-! # Axiom-hygiene gates

Building this library runs `GebLeanMeta.detectNonstandardAxiom` over
`GebLean.*`, `GebLeanTests.*`, and the vendored `Geb.*` tree via
`#lint only` gates. A non-standard axiom dependency fails the build.
-/
