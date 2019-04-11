\documentclass[]{article}

\usepackage{agdon}

\hypersetup{
            pdftitle={Untyped Allocation},
            pdfborder={0 0 0},
            breaklinks=true}

\usepackage{minted}

\title{Untyped Allocation}

\author{Dan Pittman dan@auxon.io}

\begin{document}

\begin{code}[hide]
{-# OPTIONS --safe #-}

module Ferros.Resource.Untyped.Base where

open import Data.Bool
open import Data.Fin hiding (pred)
open import Data.Nat
open import Data.Product
open import Data.Vec
\end{code}

\maketitle

In seL4 parlance, an \texttt{Untyped} is a kernel object representing
a yet-to-be-spoken-for chunk of physical memory. When a kernel object
is created, it must be done so through the seL4 system call
\texttt{seL4\_Untyped\_Retype}. \texttt{seL4\_Untyped\_Retype} take an
untyped kernel object, an object representing the kernel object to
retype this untyped chunk into, as well as the target object's
\emph{size}. That size is used by the kernel to track offsets in an
untyped object. Sizes are described in terms of the number of "bits"
in the object's size, where a bit $x$ is used in the following
equation $2^x = \text{Size}$. For example, a object whose size is $4$,
can be thought of as $2^4$ bytes, or 16 bytes.

Because \texttt{Untyped}s are themselves kernel objects with an
associated, but variable, size, they can also be the target of a
\texttt{seL4\_Untyped\_Retype} invocation. In Ferros this is common
practice: A process acquires an \texttt{Untyped} large enough to hold
all of the capabilities it intends to create, then breaks that object
down into the necessary sizes in a $\text{log}_2$ fashion. I.e., an
untyped object of size \texttt{6} can be broken into 2 of size
\texttt{5}, 4 of size \texttt{4}, 8 of size \texttt{3}, and so on.

The buddy allocator wraps an \texttt{Untyped}, or a set of
\texttt{Untyped}s, and does this $\text{log}_2$ break down
automatically by being given the desired size and then recursively
breaking down the \texttt{Untyped} object until one of the requested
size is available.

\begin{code}
buddy : ∀ n → Vec ℕ (suc n)
buddy zero = 1 ∷ []
buddy (suc n) = 0 ∷ buddy n
\end{code}

\begin{code}[hide]
record GetUtState (length : ℕ) : Set where
  field
    uts : Vec ℕ length
    idx : ℕ
    splits : ℕ
    done : Bool

open GetUtState

private
  is-zero : ℕ → Bool
  is-zero zero = true
  is-zero (suc n) = false
\end{code}

\begin{code}
get-untyped : ∀ {n} →  Fin n → Vec ℕ n → ℕ × Vec ℕ n
get-untyped index untypeds =
  let state = foldr GetUtState
                    fold-ut
                    record { uts = []
                    ; idx = (toℕ index)
                    ; splits = 0
                    ; done = false
                    }
                    untypeds
  in (splits state) , (uts state)
  where
    fold-ut : ∀ {n} ℕ → GetUtState n → GetUtState (suc n)
    fold-ut ut state with done state | is-zero (idx state) | is-zero ut

    -- We've found the untyped we're looking for and can be done.  We
    -- just tack on the remaining untypeds as they are.
    ... | true | _ | _ = record { uts = ut ∷ (uts state)
                         ; idx = (idx state)
                         ; splits = (splits state)
                         ; done = (done state)
                         }

    -- We haven't reached our desired untyped size yet, our index is
    -- non-zero
    ... | false | false | _ = record { uts = ut ∷ (uts state)
                              ; idx = pred (idx state)
                              ; splits = (splits state)
                              ; done = (done state)
                              }

    -- The index is zero and this cell has an untyped for us to
    -- take. Take it, mark it as done, move on.
    ... | false | true | false = record { uts = (pred ut) ∷ (uts state)
                                 ; idx = (idx state)
                                 ; splits = (splits state)
                                 ; done = true
                                 }

    -- We've reached our index (or moved past it), and have not yet
    -- found an untyped of the right size. So we add one untyped in
    -- this cell, and count our splits.
    ... | false | true | true = record { uts = (suc ut) ∷ (uts state)
                                ; idx = (idx state)
                                ; splits = suc (splits state)
                                ; done = (done state)
                                }
\end{code}
\end{document}
