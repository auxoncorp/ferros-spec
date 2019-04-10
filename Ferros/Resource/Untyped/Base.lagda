\documentclass[]{article}

\usepackage{agdon}

\hypersetup{
            pdftitle={Untyped Allocation}
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
open import Data.Nat
open import Data.Vec
open import Data.Fin hiding (_-_)

_-_ : ℕ → ℕ → ℕ
(suc x) - (suc y) = x - y
zero - (suc y) = zero
zero - zero = zero
x@(suc _) - zero = x

buddy : ∀ n → Vec ℕ (suc n)
buddy zero = 1 ∷ []
buddy (suc n) = 0 ∷ buddy n

is-present : ℕ → Bool
is-present (suc n) = true
is-present zero = false

split-ut : ∀ {n} → Vec ℕ n → Vec ℕ n
split-ut (y ∷ ys) with is-present y
... | true = y - 1 ∷ ys
... | false = y Data.Nat.+ 1 ∷ split-ut ys
split-ut [] = []

get-ut : ∀ {n} → Fin n → Vec ℕ n → Vec ℕ n
get-ut zero (x ∷ xs) with is-present x
... | true = (x - 1 ∷ xs)
... | false = let ss = split-ut (x ∷ xs)
              in (head ss) - 1 ∷ tail ss
get-ut (suc n) (x ∷ xs) = x ∷ get-ut n xs
\end{code}

\maketitle
