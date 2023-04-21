# Architecture

## Translation

The Tetragon compiler defines three internal languages, which act as intermediate representations: Base, June, and Flow.

- Base is the target of the elaborator, and acts as a faithful embedding of Tetragon.
- June is the target of the hoister, which performs closure conversion by transforming functions into first-order procedures.
- Flow is the target of the sequentializer, which makes control flow explicit by converting to continuation-passing style.