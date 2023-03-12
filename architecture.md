# Architecture

## Translation

The Tetragon compiler defines three internal languages, which act as intermediate representations: Base, Cypress, and Firefly.

- Base is the target of the elaborator, and acts as a semantic embedding of Tetragon.
- Cypress is the target of the continuation-passing-style (CPS) converter, which makes control flow explicit.
- Firefly is the target of the hoister, which performs closure conversion and lambda lifting, transforming functions into first-order procedures.