module Algebra.Lib where

open import Function using () renaming (id to idᶠ ; _∘_ to _∘ᶠ_) public

open import Level using (0ℓ ; suc)
open import Categories.Category
  hiding (_[_,_] ; _[_∘_] ; _[_≈_])
  renaming (Category to LCategory) public

open import Data.Product using (_,_ ; proj₁ ; proj₂) renaming (_×_ to _‵×_) public

open import Categories.Monad public
open import Categories.Monad.Strong public

Category = LCategory 0ℓ 0ℓ 0ℓ
module Category = LCategory

open import Categories.Functor using (Functor; Endofunctor; _∘F_) renaming (id to idF) public

open import Categories.Category.Cartesian public
open import Categories.Category.Cocartesian public
open import Categories.Category.Distributive public

open import Categories.Morphism public
