{-# OPTIONS --safe #-}

module Ferros.Prelude where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool

ℕ-sub : (x y : ℕ) → (y ≤ x) → ℕ
ℕ-sub x .zero z≤n = x
ℕ-sub ._ ._ (s≤s p) = ℕ-sub _ _ p

invert-ℕ-sub : ∀ x y → (p : y ≤ x) → (ℕ-sub x y p) + y ≡ x
invert-ℕ-sub x .zero z≤n = +-identityʳ x
invert-ℕ-sub (suc x) (suc y) (s≤s p) = begin
  (ℕ-sub (suc x) (suc y) (s≤s p)) + suc y   ≡⟨ +-suc (ℕ-sub (suc x) (suc y) (s≤s p)) y ⟩
  suc ((ℕ-sub (suc x) (suc y) (s≤s p)) + y) ≡⟨ cong suc (invert-ℕ-sub x y p) ⟩
  suc x
  ∎ where open ≡-Reasoning
