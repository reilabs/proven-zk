# Contributing

This document exists as a brief introduction for how you can contribute to this
repository. It includes a guide to
[the structure of the repository](#repository-structure),
[building and testing](#building-and-testing) and
[getting your code on `main`](#getting-your-code-on-main).

If you are new to Lean, you can find a guide to
[getting started with Lean]A(#new-to-lean) at the bottom of this file.

## Repository Structure

This repository consists only of the ProvenZK library and any supporting code,
with the major components as follows:

- [`lakefile.lean`](./lakefile.lean): The definition for the package and its
  dependencies.
- [`ProvenZK.lean`](./ProvenZk.lean): The entry point for the library itself.
- [`ProvenZK`](./ProvenZk): The components of the library. The main interface to
  the library lives in this folder, and supporting functionality in subfolders
  of this folder.

For a more detailed overview of the components provided by this repository,
please see the [section on components](./README.md#components) in the
[readme](./README.md).

## Building and Testing

There are no functional tests in this library, with it instead relying on highly
constrained type signatures to provide correctness. This means that building the
library is sufficient to check that it makes sense.

You can build the library as follows.

1. Clone the repository into a location of your choice.

```sh
git clone https://github.com/reilabs/proven-zk proven-zk
```

2. Build it, assuming that you have the `lake` binary available in your path.

```sh
cd proven-zk
lake build
```

## Getting Your Code on `main`

This repository works on a fork and
[pull request](https://github.com/reilabs/proven-zk/pulls) workflow, with code
review and CI as an integral part of the process. This works as follows:

1. If necessary, you fork the repository, but if you have access to do so please
   create a branch.
2. You make your changes on that branch.
3. Pull request that branch against main.
4. The pull request will be reviewed and CI will be run on it.
5. Once the reviewer(s) have accepted the code and CI has passed, the code will
   be merged to `main`.

## New to Lean?

If you are new to working with [Lean](https://leanprover.github.io), the best
starting point is the [Lean 4 Manual](https://leanprover.github.io/lean4/doc/).

While that guide contains sections on using Lean for both theorem proving and as
a programming language, we recommend following the
[theorem proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
tutorial. We also recommend looking at
[mathematics in lean](https://leanprover-community.github.io/mathematics_in_lean/index.html),
and the documentation for [mathlib 4](https://leanprover-community.github.io/mathlib4_docs/)
as the concepts there are used in this library.

Note that many of the resources on lean are for the old Lean 3 version. This
project, and Reilabs in general, make use of the new Lean 4 implementation for
its many
[enhancements](https://leanprover.github.io/lean4/doc/lean3changes.html). There
is no compatibility between the two versions, so please check that any resources
you find are for the correct version.

