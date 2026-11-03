# dev-env-lib

The library extraction is in progress. The generic CLI and shared modules can be
built and tested with Zig 0.17:

```sh
zig fmt --check src test build.zig
zig build test --summary all
zig build
```

The installer engine currently requires an environment-provided catalog; the
standalone test step covers shared and CLI modules, installer types, and the
resolver. Consumer integration tests exercise an installer with a catalog.
Ubuntu 24.04 is the supported platform. The CLI and installer use protocol 3.

The [architecture](docs/ARCHITECTURE.md), [protocol](docs/protocol.md),
[resolution](docs/resolution.md), and [state model](docs/state-model.md)
describe the generic implementation.

Run the Lean proofs and axiom audit with:

```sh
formal/run.sh
```

CI runs the Zig checks and Lean verification in independent jobs. See
[formal verification](docs/formal-verification.md) for proof coverage,
assumptions, and limitations.
