module Nominal where

record struct : Set₁ where
  field
    name : Set
    _≠_ : name → name → Set
