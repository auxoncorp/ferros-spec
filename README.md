# Ferros Specifications

A repository containing specifications and proofs about Ferros.

## Installation

_NB: The author assumes you're using Emacs to hack on Agda things._

While what it means to "install" `ferros-spec` is ambiguous, to _use_
it—that is, to open it and make `C-c C-l` happy—you'll first need a
functional installation of Agda.

### I. Installing Agda

1. Install [Stack](https://docs.haskellstack.org/en/stable/README/).

		$ curl -sSL https://get.haskellstack.org/ | sh

1. Clone the Agda source.

		$ git clone git@github.com:agda/agda.git

1. Use Stack to build and install Agda.

		$ cd agda
		$ stack --stack-yaml stack-8.6.4.yaml install

1. You should see a few lines stating that two binaries were installed
   `agda` and `agda-mode`. `agda-mode` is the Emacs integration. To
   hook Agda up to Emacs, run that command and tell it to set itself
   up.

		$ agda-mode setup

   If this is not your first go around with an Agda installation, use
   `compile` rather than `setup`. This does the elisp complilation
   with the fresh source code, but doesn't touch your `init.el` file
   again.

   _NB: It *will not* work if you've already run `setup` to do it
   again after an update. The first thing that `setup` does is check
   your `init.el` file for the presence of an Agda config. If it's
   already there, it does nothing._

### II. Configuring Agda

Agda's "library system" is... weird, in that it doesn't really have
one. What it _does_ have, is a collection of text files which help the
compiler find the right source files. Here's what you need.

#### 1. `$AGDA_DIR`

By default, it's `~/.agda`:

> The AGDA_DIR defaults to ~/.agda on unix-like systems[.]

[_The Agda docs_](https://agda.readthedocs.io/en/latest/tools/package-system.html)

Just leave it there. Don't rock the boat. I'm fairly sure that this
one in particular _will_ capsize.

`$AGDA_DIR` should contain the following files:

	$ tree ~/.agda
	/home/dpitt/.agda
	├── defaults
	└── libraries

#### 2. Libraries

`libraries` _registers_ Agda libraries through a path to an Agda
library file. `Ferros` has a library file called `ferros.agda-lib`
which you can take a look at if you'd like an example, or you can read
more
[here](https://agda.readthedocs.io/en/latest/tools/package-system.html).

Inside `libraries` you should add a path to `Ferros`'s library file:

	$ cat ~/.agda/libraries
	/home/dpitt/src/ferros-spec/ferros.agda-lib

#### 3. Defaults

`defaults` contains registered library names which you would like to
be loaded *any* time you open an Agda file. Let's get setup with the
Agda std-lib for an example.

* Clone `agda-stdlib`. I'm keeping the standard library in my `~/.agda` folder.

		$ git clone git@github.com:agda/agda-stdlib.git ~/.agda/agda-stdlib

* Register it in `libraries`.

		$ echo "/home/dpitt/.agda/agda-stdlib/standard-library.agda-lib" >> ~/.agda/libraries

* Include it in defaults.

		$ echo standard-library >> ~/.agda/defaults

Now modules from the standard library can be imported any time you
open an Agda file.

### III. Cubical Agda

Ferros makes use of an Agda library called `cubical`. If you're
insterested in what cubical Agda is, read more
[here](https://agda.readthedocs.io/en/latest/language/cubical.html?highlight=cubical).

All you need to know for the purposes of getting up and running with
Ferros is that one must clone `agda/cubical`, and register it in
`libraries` like we did with `Ferros` in the previous section.

## Latex

There exists files in the spec which are literate Agda files, in
particular those that contain the types we wish to prove certain
properties about. PDFs can be generated from those files by using the
`latex` make directive:

	$ make latex

When this command completes, you will find PDFs which correspond to
the Agda files in the `latex/` directory.
