{-# OPTIONS --safe #-}

module Presheaf.Everything where

open import Presheaf.Base
open import Presheaf.CartesianClosure
open import Presheaf.Properties

open import Presheaf.Functor.Possibility.Base
open import Presheaf.Functor.Possibility.Properties
open import Presheaf.Functor.Possibility.Pointed
open import Presheaf.Functor.Possibility.Joinable
open import Presheaf.Functor.Possibility.Monad

open import Presheaf.Functor.Possibility.Strong.Base
open import Presheaf.Functor.Possibility.Strong.Pointed
open import Presheaf.Functor.Possibility.Strong.Joinable

-- requires --with-K
open import Presheaf.Functor.Cover.Base
open import Presheaf.Functor.Cover.Pointed
open import Presheaf.Functor.Cover.Strong.Base
--open import Presheaf.Functor.Cover.Joinable

open import Presheaf.Functor.Lax
